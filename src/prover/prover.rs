use mini_groth16::{parse_circuit,load_witness_values,get_l_r_o_matrix,get_polynomials,compute_t_poly};
use ark_ff::{Fp,Fp2, MontBackend,QuadExtField,Fp2ConfigWrapper,UniformRand};
use ark_bn254::{Fr,FqConfig,Fq2Config,FrConfig, G1Projective as G, G2Projective as G2};
use rand::rngs::OsRng; 
use ark_serialize::CanonicalDeserialize;
use ark_ec::short_weierstrass::Projective;
use ark_bn254::g1::Config;
use ark_bn254::g2::Config as Config2;
use ark_serialize::CanonicalSerialize;
use std::io::{Result,Read,Cursor};
use std::fs::File;
use ark_poly::univariate::DenseOrSparsePolynomial;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use std::ops::Mul;
use base64::{engine::general_purpose, Engine as _}; // Import the Engine trait


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

// F(X) == Sum i(wi * Fi(X)) 
fn compute_complete_poly(polynomial_list:Vec<DensePolynomial<Fp<MontBackend<FrConfig, 4>, 4>>>,witness_values:Vec<Fr>) -> DensePolynomial<Fp<MontBackend<ark_bn254::FrConfig, 4>, 4>>{

    // Compute B(X) = Sum i (wi*Ri(x))
    let mut f_x = DensePolynomial::from_coefficients_vec(vec![Fr::from(0u8)]);//0

    for (f_poly,witness_val) in polynomial_list.iter().zip(witness_values){

        let witness_poly = DensePolynomial::from_coefficients_vec(vec![witness_val]);
        f_x = f_x + f_poly*witness_poly;
    }
    f_x
}


//Read witness values
fn get_witness(solution_name_list:Vec<String>)->Vec<Fr>{
    //Read the witness json file and sort according to the circuit
    let mut witness_values_json = load_witness_values("./src/prover/witness.json").unwrap();
    witness_values_json.insert("1".to_string(), "1".into());

    //Save witness values
    let mut witness_values:Vec<Fr> = Vec::new();

    for witness_name in solution_name_list{
        let does_exist = witness_values_json.contains_key(&witness_name);
        match does_exist {
            true =>{
                let var_value = witness_values_json.get(&witness_name).unwrap();
                let var_value_str = var_value.as_str().unwrap();

                //If the value is negative
                if var_value_str.contains('-'){
                    // Remove negativ sign
                    let rep = var_value_str.replace('-', "");
                    let var_value_u8 = rep.parse::<u8>().unwrap();
                    let var_value_fr = Fr::from(var_value_u8);
                    let neg_var_value_fr = -var_value_fr;
                    witness_values.push(neg_var_value_fr);
                }else{
                    let var_value_u8 = var_value_str.parse::<u8>().unwrap();
                    let var_value_fr = Fr::from(var_value_u8);
                    witness_values.push(var_value_fr);
                }

            }
            false => panic!("Variable: {:?} not found in the witness file",&witness_name)
        }   

    }

    witness_values
    
}

//Generate proof string
fn generate_proof_string(proof:Vec<ProjectiveConfigType>)->String{
    let mut proof_binary:Vec<u8> = Vec::new();
    for (_,p) in proof.iter().enumerate(){
        let(x,y,z) = p.get_coordinates();

        let element_x = x;
        let element_y = y;
        let element_z = z;

        let mut serialized_data_x = Vec::new();
        let mut serialized_data_y = Vec::new();
        let mut serialized_data_z = Vec::new();

        element_x.serialize_uncomp(&mut serialized_data_x);
        element_y.serialize_uncomp(&mut serialized_data_y);
        element_z.serialize_uncomp(&mut serialized_data_z);

        let x_len: Vec<u8> = vec![serialized_data_x.len() as u8];
        let y_len: Vec<u8> = vec![serialized_data_y.len() as u8];
        let z_len: Vec<u8> = vec![serialized_data_z.len() as u8];

        proof_binary.extend(x_len);
        proof_binary.extend(serialized_data_x);
        proof_binary.extend(y_len);
        proof_binary.extend(serialized_data_y);
        proof_binary.extend(z_len);
        proof_binary.extend(serialized_data_z);        
    }

    let proof_string = general_purpose::STANDARD.encode(proof_binary.clone());
    proof_string
    
}

fn main(){

    let (constraint_list,solution_name_list,_) = parse_circuit("./groth.circuit");
    
    //Save witness values
    let witness_values:Vec<Fr> = get_witness(solution_name_list.clone());

    
    //Read proving key
    let n = constraint_list.len();//No of gates
    let l: usize = 1; //Prv witness list seperator
    let pk_seperator = 3+2*witness_values.len()+n-1+witness_values.len()-2+1; //(Seperator for g1 and g2 elements) +1 at end for starting index of g2
    let loaded_proving_key = load_key_from_file("./proving_key.bin",pk_seperator as u8).unwrap();
    
    // Extract elements from the proving key
    let delta_g1 = extract_g1_element(loaded_proving_key[0][0].clone());
    let alpha_g1 = extract_g1_element(loaded_proving_key[0][1].clone());
    let beta_g1 = extract_g1_element(loaded_proving_key[0][2].clone());

    let li_poly_one = loaded_proving_key[1].clone();
    let ri_poly_one = loaded_proving_key[2].clone();
    let h_z_g1_list = loaded_proving_key[3].clone();
    let li_prv_one = loaded_proving_key[4].clone();

    let delta_g2 = extract_g2_element(loaded_proving_key[5][0].clone());
    let beta_g2 = extract_g2_element(loaded_proving_key[5][1].clone());
    let ri_poly_two = loaded_proving_key[6].clone();

    //Sample random r1 and r2
    let mut rng = OsRng;
    let r1 = Fr::rand(&mut rng);
    let r2 = Fr::rand(&mut rng);
    let r1_delta = delta_g1.mul(r1);
    let r2_delta = delta_g2.mul(r2);
    let r2_delta_g1 = delta_g1.mul(r2);


    let (l_matrix,r_matrix,o_matrix) = get_l_r_o_matrix(solution_name_list.clone(),constraint_list.clone());
    let l_polynomial_list = get_polynomials(l_matrix.clone());
    let r_polynomial_list = get_polynomials(r_matrix);
    let o_polynomial_list = get_polynomials(o_matrix);

    // Compute t(x) = (x-1)(x-2)..(x-n)  [Vanishing polynomial]
    let t_polynomial = compute_t_poly(n);

    // Compute  [A]1
    let mut a_commitment_g1 = alpha_g1 + r1_delta;

    // Sum(wi * Li(tau))
    for (val,witness_val) in li_poly_one.iter().zip(&witness_values){
        let val_g1 = extract_g1_element(val.clone());
        let witness_val_g1 = val_g1.mul(witness_val);
        a_commitment_g1 = a_commitment_g1 + witness_val_g1;
        
    }

    // Compute [B]2
    let mut b_commitment_g2 = beta_g2 + r2_delta;

    // Sum(wi * Ri(tau))
    for (val,witness_val) in ri_poly_two.iter().zip(&witness_values){
        let val_g2 = extract_g2_element(val.clone());
        let witness_val_g2 = val_g2.mul(witness_val);
        b_commitment_g2 = b_commitment_g2 + witness_val_g2;
        
    }


    // Compute [B]1
    let mut b_commitment_g1 = beta_g1 + r2_delta_g1;

    // Sum(wi * Ri(tau))
    for (val,witness_val) in ri_poly_one.iter().zip(&witness_values){
        let val_g1 = extract_g1_element(val.clone());
        let witness_val_g1 = val_g1.mul(witness_val);
        b_commitment_g1 = b_commitment_g1 + witness_val_g1;
        
    }


    // Compute A(X) = Sum i (wi*Li(x)) , B(X) = Sum i (wi*Ri(x)) , O(X) = Sum i (wi*Oi(x))
    let a_x = compute_complete_poly(l_polynomial_list.clone(),witness_values.clone());
    let b_x = compute_complete_poly(r_polynomial_list.clone(),witness_values.clone());
    let c_x = compute_complete_poly(o_polynomial_list.clone(),witness_values.clone());
    let p_x = a_x.clone().mul(b_x.clone()) - c_x.clone();
    let (h_x,_)= DenseOrSparsePolynomial::from(p_x.clone()).divide_with_q_and_r(&DenseOrSparsePolynomial::from(t_polynomial.clone())).unwrap();


    // Check the poylnomials
    // assert_eq!(a_x*b_x - c_x.clone(), h_x.clone()*t_polynomial,"Not equal polynomial evaluation"); // Right till here

    //Compute [C]1
    let mut c_commitment_g1 = a_commitment_g1.mul(r2) + b_commitment_g1.mul(r1) - delta_g1.mul(r1*r2);

    // Add (H(tau)T(tau))/delta to [C]1
    for (h_z_commit,h_x_coeff) in h_z_g1_list.iter().zip(h_x.coeffs()){
        let h_z_commit_g1 = extract_g1_element((*h_z_commit).clone());
        c_commitment_g1 = c_commitment_g1 + h_z_commit_g1.mul(h_x_coeff);

    }

    //Get private witness values [l+1 ..m ]
    let (_,prv_witness_values) = witness_values.split_at(l+1);
    // Add (wi*Liprv(tau))/delta to [C]1
    for (li_commit,witness_val) in li_prv_one.iter().zip(prv_witness_values){
        let li_commit_g1 = extract_g1_element((*li_commit).clone());
        let element = li_commit_g1.mul(witness_val);
        c_commitment_g1 = c_commitment_g1 + element;
        
    }

    //Combine proofs
    let proof:Vec<ProjectiveConfigType> = vec![
        ProjectiveConfigType::GOne(a_commitment_g1),
        ProjectiveConfigType::GOne(c_commitment_g1),
        ProjectiveConfigType::GTwo(b_commitment_g2),
    ];

    let proof_string = generate_proof_string(proof);
    println!("Proof: {}",proof_string);

}