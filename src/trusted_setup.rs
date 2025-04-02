use std::fs::File;
use std::{vec,ops::Mul};
use ark_bn254::{Fr,FqConfig,Fq2Config, G1Projective as G, G2Projective as G2};
use ark_ff::fields::Field;
use ark_ec::PrimeGroup;
use ark_ff::{UniformRand, Zero};
use ark_poly::DenseUVPolynomial;
use rand::rngs::OsRng; 
use ark_ec::short_weierstrass::Projective;
use ark_ff::{Fp, MontBackend,QuadExtField,Fp2ConfigWrapper};
use ark_serialize::CanonicalSerialize;
use ark_bn254::g1::Config;
use ark_bn254::g2::Config as Config2;
use std::io::Result;
use std::io::prelude::*;
use mini_groth16::{parse_circuit,get_polynomials,get_tau_k,compute_t_poly,get_l_r_o_matrix};


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
fn save_key_to_file(key:Vec<Vec<ProjectiveConfigType>>,file_name:&str) -> Result<()>{
    let mut file = File::create(file_name).unwrap();
    const DELIMITER:&[u8] = &[0];
    for vector in key {
        let mut element_written_count = 0;
        for element in vector {
            let(x,y,z) = element.get_coordinates();

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

            file.write_all(&x_len).unwrap();
            file.write_all(&mut serialized_data_x).unwrap();

            file.write_all(&y_len).unwrap();
            file.write_all(&mut serialized_data_y).unwrap();

            file.write_all(&z_len).unwrap();
            file.write_all(&mut serialized_data_z).unwrap();

            element_written_count = element_written_count + 1;
        }
        file.write_all(DELIMITER)?; // Write delimiter after vector element
    }

    Ok(())
}

fn main() {
    let (constraint_list,solution_name_list,_) = parse_circuit("./groth.circuit");
    let (l_matrix,r_matrix,o_matrix) = get_l_r_o_matrix(solution_name_list.clone(),constraint_list.clone());
    //-------------------------------------------------------------------------
    // QAP
    let l_polynomial_list = get_polynomials(l_matrix.clone());
    let r_polynomial_list = get_polynomials(r_matrix);
    let o_polynomial_list = get_polynomials(o_matrix);

    let n = l_matrix.len();

    // Compute t(x) = (x-1)(x-2)..(x-n)  [Vanishing polynomial]
    let t_polynomial = compute_t_poly(n);

    // Trusted setup-------------------------------------
    //Compute random values
    let mut rng = OsRng;
    let g1 = G::generator(); //Generator on the curve
    let g2 = G2::generator(); //Generator on the curve G2projective
    
    let alpha = Fr::rand(&mut rng);
    let beta = Fr::rand(&mut rng);
    let gamma = Fr::rand(&mut rng);
    let delta = Fr::rand(&mut rng);
    let tau = Fr::rand(&mut rng);

    //Commitments
    let alpha_g1 = g1.mul(alpha); //[alpha]1
    let beta_g1 = g1.mul(beta); //[beta]1
    let beta_g2 = g2.mul(beta);
    let delta_g1 = g1.mul(delta); //[delta]1
    let alpha_g2 = g2.mul(alpha); //[alpha]2
    let gamma_g2 = g2.mul(gamma);//[gamma]2
    let delta_g2 = g2.mul(delta); //[delta]2


    // Compute powers of tau
    let mut powtau_one :Vec<ProjectiveConfigType>= Vec::new();// [[t^i]1.. ] for i = 0 -> 2n-2

    // Compute powers of tau commitments: [[t^i]1.. ] for i = 0 -> 2n-2
    for i in 0..=(2*n-2){
        if i == 0{
            let tau_0 = Fr::from(1u8);
            let element = g1.mul(tau_0);
            powtau_one.push(ProjectiveConfigType::GOne(element));
        }else{
            let tau_i = get_tau_k(tau,i);
            let element = g1.mul(tau_i);
            powtau_one.push(ProjectiveConfigType::GOne(element));
        }
    }

    let mut powtau_two :Vec<ProjectiveConfigType>= Vec::new();// [[t^i]2.. ] for i = 0 -> n-1

    // Compute powers of tau commitments: [[t^i]2.. ] for i = 0 -> n-1
    for i in 0..=(n-1){
        if i == 0{
            let tau_0 = Fr::from(1u8);
            let element = g2.mul(tau_0);
            powtau_two.push(ProjectiveConfigType::GTwo(element));
        }else{
            let tau_i = get_tau_k(tau,i);
            let element = g2.mul(tau_i);
            powtau_two.push(ProjectiveConfigType::GTwo(element));
        }

    }

    // T(tau) 
    let mut t_eval = Fr::from(0u8);

    for (i,t_coeff) in t_polynomial.coeffs().iter().enumerate(){
        if i == 0{
            let tau_0 = Fr::from(1u8);
            let element = *t_coeff*tau_0;
            t_eval = t_eval + element;

        }else{
            let tau_i = get_tau_k(tau,i);
            let element = *t_coeff*tau_i;
            t_eval = t_eval + element;
        }
    }

    // [(ti * T(tau))/delta] for i= 0 -> n-2
    let mut h_z_g1_list = Vec::new();
    for i in 0..=(n-2){
        if i == 0{
            let tau_0 = Fr::from(1u8);
            let element = g1.mul(tau_0 * t_eval * delta.inverse().unwrap());
            h_z_g1_list.push(ProjectiveConfigType::GOne(element));
        }else{
            let tau_i = get_tau_k(tau,i);
            let element = g1.mul(tau_i * t_eval * delta.inverse().unwrap());
            h_z_g1_list.push(ProjectiveConfigType::GOne(element));
        }

    }

    //Defaulting [0,out] 0-l => 0-1 and [..] l+1 - m 
    let l: usize = 1;
    let mut li_pub_one:Vec<ProjectiveConfigType> = Vec::new(); // [Li(tau)/gamma..] for i =0 to l
    let mut li_prv_one:Vec<ProjectiveConfigType> = Vec::new(); // [Li(tau)/delta..] for i =l+1 to m
    let mut li_poly_one:Vec<ProjectiveConfigType> = Vec::new();
    let mut ri_poly_one:Vec<ProjectiveConfigType> = Vec::new();
    let mut ri_poly_two:Vec<ProjectiveConfigType> = Vec::new();
    let mut oi_poly_one:Vec<ProjectiveConfigType> = Vec::new();


    for (coeff_index,(l_poly,(r_poly,o_poly))) in l_polynomial_list.clone().iter().zip(r_polynomial_list.clone().iter().zip(o_polynomial_list.clone())).enumerate(){
        let l_coeffs = l_poly.coeffs();
        let r_coeffs = r_poly.coeffs();
        let o_coeffs = o_poly.coeffs();

        // Padding coeffecients
        let max_len = l_coeffs.len().max(r_coeffs.len()).max(o_coeffs.len());
        let l_coeffs_m = l_coeffs.iter().cloned().chain(std::iter::repeat(Fr::zero())).take(max_len).collect::<Vec<_>>();
        let r_coeffs_m = r_coeffs.iter().cloned().chain(std::iter::repeat(Fr::zero())).take(max_len).collect::<Vec<_>>();
        let o_coeffs_m = o_coeffs.iter().cloned().chain(std::iter::repeat(Fr::zero())).take(max_len).collect::<Vec<_>>();

        //l_elements
        let mut l_element_eval = Fr::from(0u8); //Li(tau)
        let mut r_element_eval = Fr::from(0u8); //Ri(tau)
        let mut o_element_eval = Fr::from(0u8); //Oi(tau)

        for (coeff_index_i,(l_coeff,(r_coeff,o_coeff))) in l_coeffs_m.iter().zip(r_coeffs_m.iter().zip(o_coeffs_m)).enumerate(){
            let l_element = *l_coeff * get_tau_k(tau,coeff_index_i);
            let r_element = *r_coeff * get_tau_k(tau,coeff_index_i);
            let o_element = o_coeff * get_tau_k(tau,coeff_index_i);
            
            l_element_eval = l_element_eval + l_element;
            r_element_eval = r_element_eval + r_element;
            o_element_eval = o_element_eval + o_element;

        }
        // Public polynomials 0-l
        if coeff_index <= l{
            let li = (beta*l_element_eval + alpha*r_element_eval+o_element_eval)*gamma.inverse().unwrap();
            let li_commit_pub = g1.mul(li);
            li_pub_one.push(ProjectiveConfigType::GOne(li_commit_pub));
        }else{
            //Private polynomials l+1 - m
            let li = (beta*l_element_eval + alpha*r_element_eval+o_element_eval)*delta.inverse().unwrap();
            let li_commit_prv = g1.mul(li);
            li_prv_one.push(ProjectiveConfigType::GOne(li_commit_prv));
        }

        // Li poly 
        let l_poly_commit_one = g1.mul(l_element_eval);
        let r_poly_commit_one = g1.mul(r_element_eval);
        let r_poly_commit_two = g2.mul(r_element_eval);
        let o_poly_commit_one = g1.mul(o_element_eval);

        
        li_poly_one.push(ProjectiveConfigType::GOne(l_poly_commit_one));
        ri_poly_one.push(ProjectiveConfigType::GOne(r_poly_commit_one));
        ri_poly_two.push(ProjectiveConfigType::GTwo(r_poly_commit_two));
        oi_poly_one.push(ProjectiveConfigType::GOne(o_poly_commit_one));      

    }

    let proving_key = vec![
        vec![
        ProjectiveConfigType::GOne(delta_g1),
        ProjectiveConfigType::GOne(alpha_g1),
        ProjectiveConfigType::GOne(beta_g1)],
        li_poly_one.clone(), // witness vector length
        ri_poly_one.clone(), // witness vector length
        h_z_g1_list.clone(), // 0-(n-2) where n=no of gates or l/r/o matrix size or no of operations  or n-1
        li_prv_one.clone(), // Witness vector length - pub witness length (Default witnesslength-2)
       vec![
            ProjectiveConfigType::GTwo(delta_g2),
            ProjectiveConfigType::GTwo(beta_g2)],
        ri_poly_two.clone()
    ];

    let verification_key = vec![
        vec![
            ProjectiveConfigType::GOne(alpha_g1),
        ],
        li_pub_one.clone(),
        vec![
            ProjectiveConfigType::GTwo(beta_g2),
            ProjectiveConfigType::GTwo(gamma_g2),
            ProjectiveConfigType::GTwo(delta_g2),
        ],
    ];

    //Generate proving and verification key
    let mut res = save_key_to_file(proving_key, "proving_key.bin"); // Save proving key

    match &res {
        Ok(()) => {
            println!("Proving key generated !!");
        }
        Err(msg)=>{
            println!("Failed to generate proving key: {:?}",msg);
        }
    }

    res = save_key_to_file(verification_key, "verification_key.bin"); // Save verification key

    match &res {
        Ok(()) => {
            println!("Verification key generated !!");
        }
        Err(msg)=>{
            println!("Failed to generate verification key: {:?}",msg);
        }
    }
}
