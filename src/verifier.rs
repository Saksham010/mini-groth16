use mini_groth16::{parse_circuit,load_witness_values};

use ark_ff::{Fp,Fp2, MontBackend,QuadExtField,Fp2ConfigWrapper,Zero};
use ark_bn254::{Bn254,Fr,FqConfig,Fq2Config,FrConfig, G1Projective as G, G2Projective as G2};
use rand::rngs::OsRng; 
use ark_serialize::CanonicalDeserialize;
use ark_ec::short_weierstrass::Projective;
use ark_bn254::g1::Config;
use ark_bn254::g2::Config as Config2;
use ark_serialize::CanonicalSerialize;
use std::io::{Result,Read,Cursor};
use std::fs::File;
use std::ops::Mul;
use base64::{engine::general_purpose, Engine as _}; // Import the Engine trait
use ark_ec::pairing::Pairing;
use std::env;

//For G1Projective and G2 projective coordinates
#[derive(Debug)]
#[derive(Clone)]
enum ProjectiveCoordinateType{
    C1(Fp<MontBackend<FqConfig, 4>, 4>),
    C2(QuadExtField<Fp2ConfigWrapper<Fq2Config>>)
}

trait ProjectiveCoordinateTypeT{
    fn serialize_uncomp(&self, serialized_data: &mut Vec<u8>);
}

impl ProjectiveCoordinateTypeT for ProjectiveCoordinateType{

    fn serialize_uncomp(&self, serialized_data: &mut Vec<u8>) {
        match self {
            ProjectiveCoordinateType::C1(val)=>{
                val.serialize_uncompressed(serialized_data).unwrap();
            }
            ProjectiveCoordinateType::C2(val)=>{
                val.serialize_uncompressed(serialized_data).unwrap();

            }
        }
    }

}

//For G1Projective and G2 projective elements
#[derive(Debug)]
#[derive(Clone)]
enum ProjectiveConfigType {
    GOne(Projective<Config>),
    GTwo(Projective<Config2>)
}

trait ProjectiveConfigTypeT {
    fn get_coordinates(&self)->(ProjectiveCoordinateType,ProjectiveCoordinateType,ProjectiveCoordinateType);
}

impl ProjectiveConfigTypeT for ProjectiveConfigType {
    fn get_coordinates(&self)->(ProjectiveCoordinateType,ProjectiveCoordinateType,ProjectiveCoordinateType) {

        match self {
            ProjectiveConfigType::GOne(point)=>{
                let x = ProjectiveCoordinateType::C1(point.x);
                let y = ProjectiveCoordinateType::C1(point.y);
                let z = ProjectiveCoordinateType::C1(point.z);
                (x,y,z)

            }
            ProjectiveConfigType::GTwo(point)=>{
                let x = ProjectiveCoordinateType::C2(point.x);
                let y = ProjectiveCoordinateType::C2(point.y);
                let z = ProjectiveCoordinateType::C2(point.z);
                (x,y,z)
            }
        }
    }
    
}

fn load_key_from_file(file_name:&str,g1g2_seperator_index:u8) -> Result<Vec<Vec<ProjectiveConfigType>>>{
    const DELIMITER: &[u8] = &[0]; // Inner delimiter for separating vec of elements

    let mut file = File::open(file_name).unwrap();

    let mut final_key:Vec<Vec<ProjectiveConfigType>> = Vec::new();
    let mut key_vec_inner:Vec<ProjectiveConfigType> = Vec::new();

    println!("Loading buffer....");

    //Buffer to load the file
    let mut buffer:Vec<u8> = Vec::new();
    file.read_to_end(&mut buffer).unwrap();

    println!("Buffer loaded....");

    // let mut cursor = &buffer[..];
    let mut cursor = Cursor::new(&buffer[..]);

    let mut iteration_no = 0;

    // Deserialize each values
    while (cursor.position() as usize) < cursor.get_ref().len(){ //Ignoring the last 0 delimiter

        //Read the length
        let mut element_len =[0u8];
        cursor.read_exact(&mut element_len).unwrap(); // Read x length

        //If delimeter found
        if element_len == DELIMITER{
            //Push and clear the inner vec
            final_key.push(key_vec_inner.clone());
            key_vec_inner.clear();

            //If last index continue/break
            if cursor.position() as usize == cursor.get_ref().len() {
                continue;
            }            
            //Else next element length
            cursor.read_exact(&mut element_len).unwrap(); // Read again length
        }

        iteration_no = iteration_no+1;

        let mut x_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut x_element).unwrap(); //Read x 

        cursor.read_exact(&mut element_len).unwrap(); // Read y length
        let mut y_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut y_element).unwrap(); //Read y 

        cursor.read_exact(&mut element_len).unwrap(); // Read z length
        let mut z_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut z_element).unwrap(); //Read z

        //Deseralize
        let mut cursorx = Cursor::new(x_element);
        let mut cursory = Cursor::new(y_element);
        let mut cursorz = Cursor::new(z_element);


        if iteration_no >= g1g2_seperator_index {
            //For G2 elements in verification key
            let deserialized_x:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursorx).unwrap();
            let deserialized_y:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursory).unwrap();
            let deserialized_z:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursorz).unwrap();
    
            let element:Projective<Config2> = G2::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
            key_vec_inner.push(ProjectiveConfigType::GTwo(element)); //Push the element
    
        }else{
    
            let deserialized_x:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorx).unwrap();
            let deserialized_y:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursory).unwrap();
            let deserialized_z:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorz).unwrap();
    
            let element:Projective<Config> = G::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
    
            key_vec_inner.push(ProjectiveConfigType::GOne(element)); //Push the element
        }

    }
    Ok(final_key)
    
}

fn extract_g1_element(element:ProjectiveConfigType)->Projective<Config>{
    match element {
        ProjectiveConfigType::GOne(ref elem) => elem.clone(),
        _ => panic!("Expected GOne element but found a different variant."),
    }
}

fn extract_g2_element(element:ProjectiveConfigType)->Projective<Config2>{
    match element {
        ProjectiveConfigType::GTwo(ref elem) => elem.clone(),
        _ => panic!("Expected GTwo element but found a different variant."),
    }
}

// Parse proof string
fn parse_proof(proof:&str) -> Vec<ProjectiveConfigType>{
    let proof_binary:Vec<u8> =  general_purpose::STANDARD.decode(proof).expect("Invalid proof !!");
    let mut cursor = Cursor::new(&proof_binary[..]);
    let mut iteration_no = 0;
    let mut deserialized_proof:Vec<ProjectiveConfigType> = Vec::new();

    //Deserialize proof elements
    while (cursor.position() as usize) < cursor.get_ref().len(){ 
        iteration_no = iteration_no+1;

        //Read the length
        let mut element_len =[0u8];

        cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read x length
        let mut x_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut x_element).expect("Invalid proof !!"); //Read x 

        cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read y length
        let mut y_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut y_element).expect("Invalid proof !!"); //Read y 

        cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read z length
        let mut z_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut z_element).expect("Invalid proof !!"); //Read z

        //Deseralize
        let mut cursorx = Cursor::new(x_element);
        let mut cursory = Cursor::new(y_element);
        let mut cursorz = Cursor::new(z_element);

        if iteration_no >= 3{
            //G2 elements
            let deserialized_x:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursorx).expect("Invalid proof !!");
            let deserialized_y:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursory).expect("Invalid proof !!");
            let deserialized_z:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursorz).expect("Invalid proof !!");
    
            let element:Projective<Config2> = G2::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
            deserialized_proof.push(ProjectiveConfigType::GTwo(element)); //Push the element
        }else{
            //G1 elements
            let deserialized_x:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorx).expect("Invalid proof !!");
            let deserialized_y:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursory).expect("Invalid proof !!");
            let deserialized_z:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorz).expect("Invalid proof !!");
    
            let element:Projective<Config> = G::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
            deserialized_proof.push(ProjectiveConfigType::GOne(element)); //Push the element
        }
    }

    deserialized_proof
}

fn main(){
    let args: Vec<String> = env::args().collect();
    let proof_string = &args[1];
    let deserialized_proof = parse_proof(proof_string);

    let (_,solution_name_list,_) = parse_circuit("./groth.circuit");
    let l = 1;

    // Read public witness file
    let public_witness_values_json = load_witness_values("./public_witness.json").unwrap();
    //Save witness values
    let mut public_witness_value:Vec<Fr> = Vec::new();
    for (index,witness_name) in solution_name_list.iter().enumerate(){
        if index <= l{
            let does_exist = public_witness_values_json.contains_key(witness_name);
            match does_exist {
                true =>{
                    let var_value = public_witness_values_json.get(witness_name).unwrap();
                    let var_value_str = var_value.as_str().unwrap();

                    //If the value is negative
                    if var_value_str.contains('-'){
                        // Remove negativ sign
                        let rep = var_value_str.replace('-', "");
                        let var_value_u8 = rep.parse::<u8>().unwrap();
                        let var_value_fr = Fr::from(var_value_u8);
                        let neg_var_value_fr = -var_value_fr;
                        public_witness_value.push(neg_var_value_fr);
                    }else{
                        let var_value_u8 = var_value_str.parse::<u8>().unwrap();
                        let var_value_fr = Fr::from(var_value_u8);
                        public_witness_value.push(var_value_fr);
                    }
    
                }
                false => panic!("Variable: {:?} not found in the witness file",&witness_name)
            }   
        }

    }

    let g1g2seperator = l+2+1; // 1 + l+1(0..=l) + 1(for g2 starting index)
    let loaded_verification_key = load_key_from_file("./verification_key.bin",g1g2seperator as u8).unwrap();
    
    // Extract elements from the verfication key
    let alpha_g1 = extract_g1_element(loaded_verification_key[0][0].clone());
    let li_pub_one = loaded_verification_key[1].clone();

    let beta_g2 = extract_g2_element(loaded_verification_key[2][0].clone());
    let gamma_g2 = extract_g2_element(loaded_verification_key[2][1].clone());
    let delta_g2 = extract_g2_element(loaded_verification_key[2][2].clone());

    // Extract proof elements
    let a_commitment_g1 = extract_g1_element(deserialized_proof[0].clone());
    let c_commitment_g1 = extract_g1_element(deserialized_proof[1].clone());
    let b_commitment_g2 = extract_g2_element(deserialized_proof[2].clone());

    // wpubi *Lpub(tau)/gamma  (i = 0->l)
    let mut public_g1_sum = G::zero();
    // Add (wi*Lipub(tau))/gamma to [C]1
    for (li_commit,witness_val) in li_pub_one.iter().zip(public_witness_value){
        let li_commit_g1 = extract_g1_element((*li_commit).clone());
        let element = li_commit_g1.mul(witness_val);
        public_g1_sum = public_g1_sum + element;
        
    }

    //Verification
    let left_pairing_part = Bn254::pairing(a_commitment_g1, b_commitment_g2);

    let right_pairing_one = Bn254::pairing(alpha_g1, beta_g2);
    let right_pairing_two = Bn254::pairing(public_g1_sum, gamma_g2);
    let right_pairing_three = Bn254::pairing(c_commitment_g1, delta_g2);
    let right_pairing_part = right_pairing_one + right_pairing_two + right_pairing_three;

    assert_eq!(left_pairing_part,right_pairing_part,"Invalid proof!!");
    println!("Valid proof!!");
}

