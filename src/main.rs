use std::path::Path;
use std::fs::File;
use std::io::Read;
use std::process::exit;
use std::collections::HashMap;
use std::{rc, result, vec,ops::Mul};
use ark_ec::pairing::Pairing;
use ark_poly::{polynomial, Polynomial};
use regex::Regex;
use ark_bn254::{Bn254,Fr,FqConfig,FrConfig,Fq2Config, G1Projective as G, G2Projective as G2};
use ark_ff::fields::Field;
use std::str::FromStr;
use ark_ec::PrimeGroup;
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use ark_poly::univariate::DenseOrSparsePolynomial;
use rand::rngs::OsRng; 
use ark_ec::short_weierstrass::Projective;
use ark_ff::{Fp, MontBackend,QuadExtField,Fp2ConfigWrapper};
use ark_serialize::CanonicalSerialize;
use ark_bn254::g1::Config;
use ark_bn254::g2::Config as Config2;
use serde_json::Value;
use std::io::Result;
use std::io::{BufReader};



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

//Extract coeff from string
fn get_coeff_var(data:&str)->[String;2]{
    //Process variable part first
    let re: Regex = Regex::new(r"[a-z]+[0-9]*").unwrap(); // Match a-z followed by optional digits
    let var = re.find(data).unwrap().as_str();

    // Process digit part
    let (digitpart,_) = data.split_once(var).unwrap();
    let digitvec:Vec<char> = digitpart.chars().filter(|c| c.is_digit(10)).collect();
    let coeff:String = digitvec.iter().collect();

    let result:[String;2] = [if coeff == ""{"1".to_string()}else{coeff},var.to_string()];
    result
}


// Get additative inverse
fn get_add_inv(val:Fr)->Fr{
    let add_inv = -val;
    add_inv

}

// Extracts from a constraints
fn extract_constraints<'a>(constraints:&'a str,delimiter:&str)-> HashMap<String, Vec<String>>{
    let mut solutionMap:HashMap<String,Vec<String>> = HashMap::new();

    // If a+b => (a+b)*1
    if delimiter == "+"{
        let (lr,out) = constraints.split_once("=").unwrap();
        let (left_one,left_two) = lr.split_once("+").unwrap();
        let res_one:[String;2] = get_coeff_var(left_one);
        let res_two:[String;2] = get_coeff_var(left_two);

        let lcoeff_one = res_one[0].clone();
        let lvar_one = res_one[1].clone();
        
        let lcoeff_two = res_two[0].clone();
        let lvar_two = res_two[1].clone();

        let rcoeff = "1".to_string();
        let rvar = "NONE".to_string();

        //Filter out var and coeff
        let res_out:[String;2] = get_coeff_var(out);
        let ocoeff = res_out[0].clone();
        let ovar = res_out[1].clone();


        // Create and return hashmap
        solutionMap.insert("left_coeff".to_string(),vec![lcoeff_one,lcoeff_two]);
        solutionMap.insert("left_var".to_string(), vec![lvar_one,lvar_two]);

        solutionMap.insert("right_coeff".to_string(),vec![rcoeff]);
        solutionMap.insert("right_var".to_string(), vec![rvar]);

        solutionMap.insert("out_coeff".to_string(),vec![ocoeff]);
        solutionMap.insert("out_var".to_string(), vec![ovar]);
        return solutionMap;
    }else if delimiter == "-"{
        //If a-b => (a+(-b))*1 => (a+(addinv(b)))*1
        let (lr,out) = constraints.split_once("=").unwrap();
        let (left_one,left_two) = lr.split_once("-").unwrap();
        let res_one:[String;2] = get_coeff_var(left_one);
        let res_two:[String;2] = get_coeff_var(left_two);

        let lcoeff_one = res_one[0].clone();
        let lvar_one = res_one[1].clone();
        
        let lcoeff_two = res_two[0].clone();
        let lvar_two = res_two[1].clone();

        let one_f = Fr::from(1u8);
        let lcoeff_two_fr =  one_f * Fr::from(lcoeff_two.parse::<u8>().unwrap());
        let lcoeff_two_fr_inv = get_add_inv(lcoeff_two_fr);

        let rcoeff = "1".to_string();
        let rvar = "NONE".to_string();

        //Filter out var and coeff
        let res_out:[String;2] = get_coeff_var(out);
        let ocoeff = res_out[0].clone();
        let ovar = res_out[1].clone();

        // Create and return hashmap
        solutionMap.insert("left_coeff".to_string(),vec![lcoeff_one,lcoeff_two_fr_inv.to_string()]);
        solutionMap.insert("left_var".to_string(), vec![lvar_one,lvar_two]);

        solutionMap.insert("right_coeff".to_string(),vec![rcoeff]);
        solutionMap.insert("right_var".to_string(), vec![rvar]);

        solutionMap.insert("out_coeff".to_string(),vec![ocoeff]);
        solutionMap.insert("out_var".to_string(), vec![ovar]);

        return solutionMap;


    }else if delimiter == "/"{
        //If a-b => (a+(-b))*1 => (a+(addinv(b)))*1
        let (lr,out) = constraints.split_once("=").unwrap();
        let (left,right) = lr.split_once("/").unwrap();
        let res_left:[String;2] = get_coeff_var(left);
        let res_right:[String;2] = get_coeff_var(right);

        let lcoeff = res_left[0].clone();
        let lvar = res_left[1].clone();
        
        let rcoeff = res_right[0].clone();
        let rvar = res_right[1].clone();

        let one_f = Fr::from(1u8);
        let rcoeff_fr:Fr =  one_f * Fr::from(rcoeff.parse::<u8>().unwrap());
        let rcoeff_fr_inv = rcoeff_fr.inverse().unwrap();


        //Filter out var and coeff
        let res_out:[String;2] = get_coeff_var(out);
        let ocoeff = res_out[0].clone();
        let ovar = res_out[1].clone();

        // Create and return hashmap
        solutionMap.insert("left_coeff".to_string(),vec![lcoeff]);
        solutionMap.insert("left_var".to_string(), vec![lvar]);

        solutionMap.insert("right_coeff".to_string(),vec![rcoeff_fr_inv.to_string()]);
        solutionMap.insert("right_var".to_string(), vec![rvar]);

        solutionMap.insert("out_coeff".to_string(),vec![ocoeff]);
        solutionMap.insert("out_var".to_string(), vec![ovar]);

        return solutionMap;

    }

    // If a*b
    match constraints.split_once("*"){
        Some((left,remaining)) =>{

            //Left filter coefficient
            let res:[String;2] = get_coeff_var(left);
            let lcoeff = res[0].clone();
            let lvar = res[1].clone();


            // println!("Left Coeff: {:?}",lcoeff);
            // println!("Left var: {:?}",lvar);

            match remaining.split_once("="){
                Some((right,out))=>{
                    //Filter right coefficient
                    let res:[String;2] = get_coeff_var(right);
                    let rcoeff = res[0].clone();
                    let rvar = res[1].clone();

                    // println!("Right Coeff: {:?}",rcoeff);
                    // println!("Right var: {:?}",rvar);

                    //Filter out var and coeff
                    let res:[String;2] = get_coeff_var(out);
                    let ocoeff = res[0].clone();
                    let ovar = res[1].clone();

                    // println!("Out Coeff: {:?}",ocoeff);
                    // println!("Out var: {:?}",ovar);


                    // Create and return hashmap
                    solutionMap.insert("left_coeff".to_string(),vec![lcoeff]);
                    solutionMap.insert("left_var".to_string(), vec![lvar]);

                    solutionMap.insert("right_coeff".to_string(),vec![rcoeff]);
                    solutionMap.insert("right_var".to_string(), vec![rvar]);

                    solutionMap.insert("out_coeff".to_string(),vec![ocoeff]);
                    solutionMap.insert("out_var".to_string(), vec![ovar]);

                },
                None => {
                    print!("Constraint: {:?} does not follow standard",constraints);
                    exit(0);
                } 
            };
        },
        None => exit(0)
    };

    println!("Constraints to extract: {:?}",constraints);
    solutionMap



}
//Get slice of string
fn get_slice<'a>(data:&'a str,delimiter:&str)-> &'a str{
    let sliced = match data.split_once(delimiter){
        Some((_,b)) => b,
        None => ""
    };
    sliced
}


// Check if constraint spilt has any other operators
fn validate_operators(split_constraint:&str,delimiter:&str) -> bool{
    // let operators_list = ["*","+","-","/"];
    let operators_list = [delimiter];
    let mut found = false;

    let _ = split_constraint.chars().filter(|x| {
        for op in operators_list{
            if x.to_string() == op{
                found = true;
                break;
            }
        }
        found
    });
    found
}

//Parses circuit
fn parse_circuit(file_name:&str) -> (Vec<HashMap<String,Vec<String>>>,Vec<String>,HashMap<String,String>) {
    let path = Path::new(file_name);
    let file = File::open(path);
    let mut contents = String::new();
    let res = file.expect("Unable to open").read_to_string(&mut contents);
    let shift_operators = ["+","-","/"];

    let mut constraint_map_list:Vec<HashMap<String,Vec<String>>> = Vec::new();
    let mut cache_check:HashMap<String,String> = HashMap::new();

    let mut input_var_list:Vec<String> = Vec::new();
    let mut out_var_list:Vec<String> = Vec::new();

    //Handle error
    match res {
        Ok(_) => {
            println!("Analyzing circuit");
            println!("Contents: {:?}",contents);
            // Parse circuit
            let replaced_string = contents.replace("\r\n", ",");
            let contraints_array:Vec<&str> = replaced_string.split(',').filter(|s| !s.is_empty()).collect();
            println!("Contraints array: {:?}",&contraints_array);

            let res:Vec<&str> = contraints_array.iter().map(|val| {
                let index = val.find("*");
                
                match index {
                    Some(_) => {
                        println!("Multiplication operators found");
                        // Validate constraint
                        let sliced_constraint = get_slice(val,"*");
                        if validate_operators(sliced_constraint,"*") == true{
                            println!("Constraint: {:?} does not follow standard",val);
                            exit(0);
                        }
                        // Extract constraint
                        let extracted_constraint_map = extract_constraints(val,"*");
                        println!("Extracted constraint map : {:?}",extracted_constraint_map);
                        let out_var = extracted_constraint_map.get("out_var").unwrap()[0].clone();
                        let out_coeff = extracted_constraint_map.get("out_coeff").unwrap()[0].clone();
                        let left_var = extracted_constraint_map.get("left_var").unwrap()[0].clone();
                        let left_coeff = extracted_constraint_map.get("left_coeff").unwrap()[0].clone();
                        let right_var = extracted_constraint_map.get("right_var").unwrap()[0].clone();
                        let right_coeff = extracted_constraint_map.get("right_coeff").unwrap()[0].clone();

                        out_var_list.push(extracted_constraint_map.get("out_var").unwrap()[0].clone());
                        cache_check.insert(out_var,out_coeff);

                        // cache_check.
                        // If the left value is not already inserted
                        if cache_check.get(&left_var) == None{
                            input_var_list.push(extracted_constraint_map.get("left_var").unwrap()[0].clone());
                            cache_check.insert(left_var,left_coeff);

                        }

                        // If right value is not already inserted
                        if cache_check.get(&right_var) == None{
                            input_var_list.push(extracted_constraint_map.get("right_var").unwrap()[0].clone());
                            cache_check.insert(right_var,right_coeff);

                        }
                        
                        constraint_map_list.push(extracted_constraint_map);
                    },
                    None => {
                        // If other operator additional shifting
                        shift_operators.map(|op|{
                            let found = val.find(op);
                            println!("Found operator: {:?}",op);
                            match found{
                                Some(_)=> {
                                    // If operator matches
                                    if op == "+"{

                                        println!("Addition operators found");
                                        // Validate constraint
                                        let sliced_constraint = get_slice(val,"+");
                                        if validate_operators(sliced_constraint,"+") == true{
                                            println!("Constraint: {:?} does not follow standard",val);
                                            exit(0);
                                        }

                                        let extracted_constraint_map = extract_constraints(val,"+");
                                        println!("Extracted constraint map(ADD) : {:?}",extracted_constraint_map);
                                        let out_var = extracted_constraint_map.get("out_var").unwrap()[0].clone();
                                        let out_coeff = extracted_constraint_map.get("out_coeff").unwrap()[0].clone();
                                        let left_var = extracted_constraint_map.get("left_var").unwrap().clone();
                                        let left_coeff = extracted_constraint_map.get("left_coeff").unwrap().clone();
                                        let right_var = extracted_constraint_map.get("right_var").unwrap().clone();
                                        let right_coeff = extracted_constraint_map.get("right_coeff").unwrap().clone();
                
                                        out_var_list.push(out_var.clone()); //Unchanged
                                        cache_check.insert(out_var,out_coeff); //Unchanged 
                
                                        // cache_check.
                                        // If the left value is not already inserted
                                        for (lvar,lcoeff) in left_var.iter().zip(left_coeff){

                                            if cache_check.get(lvar) == None{
                                                input_var_list.push(lvar.clone());
                                                cache_check.insert(lvar.clone(),lcoeff);
                    
                                            }

                                        }

                                        // If right value is not already inserted
                                        for (rvar,rcoeff) in right_var.iter().zip(right_coeff){

                                            if cache_check.get(rvar) == None && rvar != "NONE"{
                                                input_var_list.push(rvar.clone());
                                                cache_check.insert(rvar.clone(),rcoeff);
                    
                                            }

                                        }
               
                                        
                                        constraint_map_list.push(extracted_constraint_map);


                                    }else if op == "-" {

                                        println!("Subtraction operators found");
                                        // Validate constraint
                                        let sliced_constraint = get_slice(val,"-");
                                        if validate_operators(sliced_constraint,"-") == true{
                                            println!("Constraint: {:?} does not follow standard",val);
                                            exit(0);
                                        }

                                        let extracted_constraint_map = extract_constraints(val,"-");
                                        println!("Extracted constraint map(SUB) : {:?}",extracted_constraint_map);
                                        let out_var = extracted_constraint_map.get("out_var").unwrap()[0].clone();
                                        let out_coeff = extracted_constraint_map.get("out_coeff").unwrap()[0].clone();
                                        let left_var = extracted_constraint_map.get("left_var").unwrap().clone();
                                        let left_coeff = extracted_constraint_map.get("left_coeff").unwrap().clone();
                                        let right_var = extracted_constraint_map.get("right_var").unwrap().clone();
                                        let right_coeff = extracted_constraint_map.get("right_coeff").unwrap().clone();
                
                                        out_var_list.push(out_var.clone()); //Unchanged
                                        cache_check.insert(out_var,out_coeff); //Unchanged 
                
                                        // cache_check.
                                        // If the left value is not already inserted
                                        for (lvar,lcoeff) in left_var.iter().zip(left_coeff){

                                            if cache_check.get(lvar) == None{
                                                input_var_list.push(lvar.clone());
                                                cache_check.insert(lvar.clone(),lcoeff);
                    
                                            }

                                        }

                                        // If right value is not already inserted
                                        for (rvar,rcoeff) in right_var.iter().zip(right_coeff){

                                            if cache_check.get(rvar) == None && rvar != "NONE"{
                                                input_var_list.push(rvar.clone());
                                                cache_check.insert(rvar.clone(),rcoeff);
                    
                                            }

                                        }
               
                                        
                                        constraint_map_list.push(extracted_constraint_map);

                                        
                                    }else if op == "/"{
                                        println!("Division operators found");
                                        // Validate constraint
                                        let sliced_constraint = get_slice(val,"/");
                                        if validate_operators(sliced_constraint,"/") == true{
                                            println!("Constraint: {:?} does not follow standard",val);
                                            exit(0);
                                        }

                                        let extracted_constraint_map = extract_constraints(val,"/");
                                        println!("Extracted constraint map(DIV) : {:?}",extracted_constraint_map);
                                        let out_var = extracted_constraint_map.get("out_var").unwrap()[0].clone();
                                        let out_coeff = extracted_constraint_map.get("out_coeff").unwrap()[0].clone();
                                        let left_var = extracted_constraint_map.get("left_var").unwrap()[0].clone();
                                        let left_coeff = extracted_constraint_map.get("left_coeff").unwrap()[0].clone();
                                        let right_var = extracted_constraint_map.get("right_var").unwrap()[0].clone();
                                        let right_coeff = extracted_constraint_map.get("right_coeff").unwrap()[0].clone();
                
                                        out_var_list.push(extracted_constraint_map.get("out_var").unwrap()[0].clone());
                                        cache_check.insert(out_var,out_coeff);
                
                                        // cache_check.
                                        // If the left value is not already inserted
                                        if cache_check.get(&left_var) == None{
                                            input_var_list.push(extracted_constraint_map.get("left_var").unwrap()[0].clone());
                                            cache_check.insert(left_var,left_coeff);
                
                                        }
                
                                        // If right value is not already inserted
                                        if cache_check.get(&right_var) == None{
                                            input_var_list.push(extracted_constraint_map.get("right_var").unwrap()[0].clone());
                                            cache_check.insert(right_var,right_coeff);
                
                                        }
                                        
                                        constraint_map_list.push(extracted_constraint_map);


                                    }else{
                                        println!("No valid operators found");
                                        exit(0);
                                    }
                                },
                                None => {}
                            }
                             
                        });
                        
                    }
                }
                
                *val
            }).collect();


        }
        Err(_) => {
            panic!("Circuit analysis failed");
        }
    }

    println!("OUTLIST: {:?}",out_var_list);
    println!("INPUTLIST: {:?}",input_var_list);

    let (last_out,auxillary)= out_var_list.split_last().unwrap();

    // [1,out,inputs,auxilliary]
    let solution_list_variable = [vec!["1".to_string()],vec![last_out.to_string()],input_var_list,auxillary.to_vec()].concat();
    println!("Solution vector name list: {:?}",solution_list_variable);

    (constraint_map_list,solution_list_variable,cache_check)


}

// Get matrix vec mul
fn get_matrix_vec_mul(matrix:Vec<Vec<Fr>>,s:Vec<Fr>)->Vec<Fr>{
    let mut result:Vec<Fr>= Vec::new();
    
    for row in matrix{
        let mut sum = Fr::from(0u8);
        for (val,sval) in row.iter().zip(s.clone()){
            sum += *val*sval;
        }
        result.push(sum);
    }
    result

}

// Interpolate polynomial
pub fn lagrange_interpolation_polynomial<F: PrimeField>(points: &[(F, F)]) -> DensePolynomial<F> {
    let zero = DensePolynomial::from_coefficients_vec(vec![F::zero()]);
    let one = DensePolynomial::from_coefficients_vec(vec![F::one()]);

    points.iter().enumerate().fold(zero, |acc, (i, &(xi, yi))| {
        let mut term = one.clone();
        let mut denominator: F = F::one();

        for (j, &(xj, _)) in points.iter().enumerate() {
            if i != j {
                term = term.mul(&DensePolynomial::from_coefficients_vec(vec![-xj, F::one()]));
                denominator *= xi - xj;
            }
        }

        
        let scalar: F = yi * denominator.inverse().unwrap();
        acc + term.mul(&DensePolynomial::from_coefficients_vec(vec![scalar,F::zero()]))
    })

}

// Get polynomials 
fn get_polynomials(matrix:Vec<Vec<Fr>>) -> Vec<DensePolynomial<ark_ff::Fp<ark_ff::MontBackend<ark_bn254::FrConfig, 4>, 4>>>{

    // Interpolate columns 
    let no_of_points = matrix.len();
    let no_of_polynomials = matrix[0].len();
    let mut poly_list:Vec<DensePolynomial<ark_ff::Fp<ark_ff::MontBackend<ark_bn254::FrConfig, 4>, 4>>> = vec![];

    let mut colno = 0;
    loop{
        if colno == no_of_polynomials{
            break;
        }
        let mut point_list:Vec<(Fr,Fr)> = vec![];
        for (rowindex,row) in matrix.iter().enumerate(){
            for (colindex,col) in row.iter().enumerate(){
    
                if colno == colindex{
                    let row_num:u8 = rowindex.try_into().unwrap();
                    let point:(Fr,Fr) = (Fr::from(row_num+1),*col);
                    point_list.push(point);
                    // println!("Point: {:?}",point);
                }
            }
        }

        // If a complete list of points interpolate
        // if colno == no_of_polynomials-1{
        let res_poly= lagrange_interpolation_polynomial(&point_list);
        poly_list.push(res_poly);

        colno += 1;
    }

    poly_list


}

// Get power of tau
fn get_tau_k(tau:Fr,times:usize)->Fr{
    let mut t_final =Fr::from(1u8);
    for _ in 0..times{
        t_final = t_final*tau;
    }
    t_final

}

//Load witness values
fn load_witness_values(path:&str) -> Result<HashMap<String,Value>>{
    let file = File::open(path).unwrap();
    let reader = BufReader::new(file);
    let witness_values:HashMap<String,Value> = serde_json::from_reader(reader).unwrap();
    Ok(witness_values)
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
fn main() {
    let (constraint_list,solution_name_list,coeff_cache) = parse_circuit("./groth.circuit");
    let mut l_matrix:Vec<Vec<Fr>> = Vec::new();
    let mut r_matrix:Vec<Vec<Fr>> = Vec::new();
    let mut o_matrix:Vec<Vec<Fr>> = Vec::new();

    println!("---------------------------------------------------------------------------------");
    println!("Solution name list: {:?}",solution_name_list);
    for constraint in constraint_list{
        let mut solution_val_list_l = vec![Fr::from(0u8);solution_name_list.len()];
        let mut solution_val_list_r = vec![Fr::from(0u8);solution_name_list.len()];
        let mut solution_val_list_o = vec![Fr::from(0u8);solution_name_list.len()];

        let out_var = constraint.get("out_var").unwrap()[0].clone();
        let out_coeff = constraint.get("out_coeff").unwrap()[0].clone();

        let left_var = constraint.get("left_var").unwrap().clone();
        let left_coeff = constraint.get("left_coeff").unwrap().clone();

        let right_var = constraint.get("right_var").unwrap().clone();
        let right_coeff = constraint.get("right_coeff").unwrap().clone();

        let index = solution_name_list.iter().position(|x| *x==out_var).unwrap();
        solution_val_list_o[index] = Fr::from(out_coeff.parse::<u8>().unwrap());

        for (lvar,lcoeff) in  left_var.iter().zip(left_coeff){
            let index = solution_name_list.iter().position(|x| x==lvar).unwrap();
            // solution_val_list[index] = Fr::from(lcoeff.parse::<u8>().unwrap());
            solution_val_list_l[index] = Fr::from_str(&lcoeff).unwrap();
        }

        for (rvar,rcoeff) in  right_var.iter().zip(right_coeff){
            if rvar != "NONE"{
                
                let index = solution_name_list.iter().position(|x| x==rvar).unwrap();
                // solution_val_list[index] = Fr::from(rcoeff.parse::<u8>().unwrap());
                solution_val_list_r[index] = Fr::from_str(&rcoeff).unwrap();

            }else if rvar == "NONE"{
                solution_val_list_r[0] = Fr::from_str(&rcoeff).unwrap();
            }
        }
        
        // solution_val_list_l[0] = Fr::from(1u8);
        // solution_val_list_r[0] = Fr::from(1u8);
        // solution_val_list_o[0] = Fr::from(1u8);

        //Push to matrix
        l_matrix.push(solution_val_list_l);
        r_matrix.push(solution_val_list_r);
        o_matrix.push(solution_val_list_o);

        // println!("Solutionval list: {:?}",solution_val_list);

    }

    println!("L_matrix: {:?}",l_matrix);
    println!("R_matrix: {:?}",r_matrix);
    println!("o _matrix: {:?}",o_matrix);

    // let solution_vector = vec![Fr::from(1u8),Fr::from(2u8),Fr::from(1u8),Fr::from(1u8),Fr::from(2u8),Fr::from(1u8),Fr::from(4u8),Fr::from(2u8),Fr::from(6u8),Fr::from(1u8),Fr::from(20u8),Fr::from(40u8),Fr::from(3u8),Fr::from(2u8)];

    // let l_s = get_matrix_vec_mul(l_matrix.clone(),solution_vector.clone());
    // let r_s = get_matrix_vec_mul(r_matrix.clone(),solution_vector.clone());
    // let o_s = get_matrix_vec_mul(o_matrix.clone(),solution_vector.clone());

    // println!("L*S Vector: {:?}",l_s);
    // println!("R*S Vector: {:?}",r_s);
    // println!("O*S Vector: {:?}",o_s);


    // let t = Fr::from_str("14592161914559516814830937163504850059032242933610689562465469457717205663745").unwrap();
    // let six_fr = Fr::from(6u8);
    // let ans = six_fr *t;

    // println!("ANS: {:?}",ans);

    //-------------------------------------------------------------------------
    // QAP
    let l_polynomial_list = get_polynomials(l_matrix.clone());
    let r_polynomial_list = get_polynomials(r_matrix);
    let o_polynomial_list = get_polynomials(o_matrix);

    let n = l_matrix.len();

    // Compute t(x) = (x-1)(x-2)..(x-n)  [Vanishing polynomial]
    let mut t_polynomial = DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]);
    for i in 1..=n{
        let rq:u8 = i.try_into().unwrap();
        let rq_poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(rq)]);
        let x_poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(0),Fr::from(1)]); // X
        let element = x_poly - rq_poly;
        t_polynomial = t_polynomial.mul(element);
    }

    println!("Vanishing polynomial: {:?}",t_polynomial);

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
    let l = 1;
    let mut li_pub_one:Vec<ProjectiveConfigType> = Vec::new(); // [Li(tau)/gamma..] for i =0 to l
    let mut li_prv_one:Vec<ProjectiveConfigType> = Vec::new(); // [Li(tau)/delta..] for i =l+1 to m
    let mut li_poly_one:Vec<ProjectiveConfigType> = Vec::new();
    let mut ri_poly_one:Vec<ProjectiveConfigType> = Vec::new();
    let mut ri_poly_two:Vec<ProjectiveConfigType> = Vec::new();
    let mut oi_poly_one:Vec<ProjectiveConfigType> = Vec::new();

    println!("--------------------------L_POLYNOMAIL LIST LEN: {:?}",l_polynomial_list.len());

    for (coeff_index,(l_poly,(r_poly,o_poly))) in l_polynomial_list.clone().iter().zip(r_polynomial_list.clone().iter().zip(o_polynomial_list.clone())).enumerate(){
        let l_coeffs = l_poly.coeffs();
        let r_coeffs = r_poly.coeffs();
        let o_coeffs = o_poly.coeffs();

        // Padding coeffecients
        let max_len = l_coeffs.len().max(r_coeffs.len()).max(o_coeffs.len());
        let l_coeffs_m = l_coeffs.iter().cloned().chain(std::iter::repeat(Fr::zero())).take(max_len).collect::<Vec<_>>();
        let r_coeffs_m = r_coeffs.iter().cloned().chain(std::iter::repeat(Fr::zero())).take(max_len).collect::<Vec<_>>();
        let o_coeffs_m = o_coeffs.iter().cloned().chain(std::iter::repeat(Fr::zero())).take(max_len).collect::<Vec<_>>();

        // println!("Before coeff index: --------------");
        println!("l_coeffs len: {}, r_coeffs len: {}, o_coeffs len: {}", l_coeffs_m.len(), r_coeffs_m.len(), o_coeffs_m.len());

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
    println!("-----------------------------------------");
    println!("LI_PUB_LEN: {:?}",li_pub_one.len());
    println!("LI_PRV_LEN: {:?}",li_prv_one.len());

    //-------------------------------------------------------------------------------------------------------------
    //Prover

    //Sample random r1 and r2
    let r1 = Fr::rand(&mut rng);
    let r2 = Fr::rand(&mut rng);
    let r1_delta = delta_g1.mul(r1);
    let r2_delta = delta_g2.mul(r2);
    let r2_delta_g1 = delta_g1.mul(r2);

    //Read the witness json file and sort according to the circuit
    let mut witness_values_json = load_witness_values("./witness.json").unwrap();
    witness_values_json.insert("1".to_string(), "1".into());

    //Save witness values
    let mut witness_values:Vec<Fr> = Vec::new();

    for witness_name in solution_name_list.clone(){
        let does_exist = witness_values_json.contains_key(&witness_name);
        match does_exist {
            true =>{
                let var_value = witness_values_json.get(&witness_name).unwrap();
                let var_value_str = var_value.as_str().unwrap();
                let var_value_u8 = var_value_str.parse::<u8>().unwrap();
                let var_value_fr = Fr::from(var_value_u8);
                witness_values.push(var_value_fr);

            }
            false => panic!("Variable: {:?} not found in the witness file",&witness_name)
        }   

    }

    println!("Witness values: {:?}",witness_values);

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

    println!("Check");


    // Compute A(X) = Sum i (wi*Li(x)) , B(X) = Sum i (wi*Ri(x)) , O(X) = Sum i (wi*Oi(x))
    let a_x = compute_complete_poly(l_polynomial_list.clone(),witness_values.clone());
    let b_x = compute_complete_poly(r_polynomial_list.clone(),witness_values.clone());
    let c_x = compute_complete_poly(o_polynomial_list.clone(),witness_values.clone());
    let p_x = a_x.clone().mul(b_x.clone()) - c_x.clone();
    let (h_x,rem)= DenseOrSparsePolynomial::from(p_x.clone()).divide_with_q_and_r(&DenseOrSparsePolynomial::from(t_polynomial.clone())).unwrap();
    // let h_x = p_x.clone()/t_polynomial.clone();
    // H_X validation
    if rem.coeffs != []{
        panic!("Error occured!! H(X) has a remainder.");
    }


    // Check the poylnomials
    assert_eq!(a_x*b_x - c_x.clone(), h_x.clone()*t_polynomial,"Not equal polynomial evaluation"); // Right till here




    //Compute [C]1
    let mut c_commitment_g1 = a_commitment_g1.mul(r2) + b_commitment_g1.mul(r1) - delta_g1.mul(r1*r2);

    // Add (H(tau)T(tau))/delta to [C]1
    for (h_z_commit,h_x_coeff) in h_z_g1_list.iter().zip(h_x.coeffs()){
        let h_z_commit_g1 = extract_g1_element((*h_z_commit).clone());
        c_commitment_g1 = c_commitment_g1 + h_z_commit_g1.mul(h_x_coeff);

    }

    //Get private witness values [l+1 ..m ]
    let (_,prv_witness_values) = witness_values.split_at(l+1);
    println!("Private witness values: {:?}",prv_witness_values);
    // Add (wi*Liprv(tau))/delta to [C]1
    for (li_commit,witness_val) in li_prv_one.iter().zip(prv_witness_values){
        let li_commit_g1 = extract_g1_element((*li_commit).clone());
        let element = li_commit_g1.mul(witness_val);
        c_commitment_g1 = c_commitment_g1 + element;
        
    }


    // Verifier

    // Read public witness file
    let public_witness_values_json = load_witness_values("./public_witness.json").unwrap();
    witness_values_json.insert("1".to_string(), "1".into());
    //Save witness values
    let mut public_witness_value:Vec<Fr> = Vec::new();
    for (index,witness_name) in solution_name_list.iter().enumerate(){
        if index <= l{
            let does_exist = public_witness_values_json.contains_key(witness_name);
            match does_exist {
                true =>{
                    let var_value = public_witness_values_json.get(witness_name).unwrap();
                    let var_value_str = var_value.as_str().unwrap();
                    let var_value_u8 = var_value_str.parse::<u8>().unwrap();
                    let var_value_fr = Fr::from(var_value_u8);
                    public_witness_value.push(var_value_fr);
    
                }
                false => panic!("Variable: {:?} not found in the witness file",&witness_name)
            }   
        }

    }

    println!("Public Witness values: {:?}",public_witness_value);

    // wpubi *Lpub(tau)/gamma  (i = 0->l)
    let mut public_g1_sum = G::zero();
    println!("Pubg1_sum: {:?}",public_g1_sum);
    // Add (wi*Lipub(tau))/gamma to [C]1
    for (li_commit,witness_val) in li_pub_one.iter().zip(public_witness_value){
        let li_commit_g1 = extract_g1_element((*li_commit).clone());
        let element = li_commit_g1.mul(witness_val);
        public_g1_sum = public_g1_sum + element;
        
    }
    println!("Pubg1_sum: {:?}",public_g1_sum);


    //Verification
    let left_pairing_part = Bn254::pairing(a_commitment_g1, b_commitment_g2);

    let right_pairing_one = Bn254::pairing(alpha_g1, beta_g2);
    let right_pairing_two = Bn254::pairing(public_g1_sum, gamma_g2);
    let right_pairing_three = Bn254::pairing(c_commitment_g1, delta_g2);
    let right_pairing_part = right_pairing_one + right_pairing_two + right_pairing_three;

    assert_eq!(left_pairing_part,right_pairing_part,"Invalid proof!!");
    println!("Valid proof");


}
