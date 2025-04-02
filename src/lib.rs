use std::path::Path;
use std::fs::File;
use std::process::exit;
use regex::Regex;
use std::collections::HashMap;
use ark_bn254::Fr;
use ark_ff::fields::Field;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use ark_ff::{PrimeField};
use std::{ops::Mul};
use std::io::{BufReader,Read,Result};
use serde_json::Value;
use std::str::FromStr;
use ark_ff::{Fp, MontBackend};
use ark_bn254::{FrConfig};


// Get power of tau
pub fn get_tau_k(tau:Fr,times:usize)->Fr{
    let mut t_final =Fr::from(1u8);
    for _ in 0..times{
        t_final = t_final*tau;
    }
    t_final

}

//Load witness values
pub fn load_witness_values(path:&str) -> Result<HashMap<String,Value>>{
    let file = File::open(path).unwrap();
    let reader = BufReader::new(file);
    let witness_values:HashMap<String,Value> = serde_json::from_reader(reader).unwrap();
    Ok(witness_values)
}


// Get slice of string
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

            match remaining.split_once("="){
                Some((right,out))=>{
                    //Filter right coefficient
                    let res:[String;2] = get_coeff_var(right);
                    let rcoeff = res[0].clone();
                    let rvar = res[1].clone();

                    //Filter out var and coeff
                    let res:[String;2] = get_coeff_var(out);
                    let ocoeff = res[0].clone();
                    let ovar = res[1].clone();

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
    solutionMap
}

// Filter negative coeff[-val]
fn shield_brack_parser(op: &str) -> String{
    let op_arr: Vec<char> = op.chars().collect();
 
    let mut start_brack_index = -1;
    let mut coeff_char_array:Vec<char> = Vec::new();

    let mut replace_pattern:Vec<String> = Vec::new();
    let mut replace_val:Vec<String> = Vec::new();

    for (index,val) in op_arr.iter().enumerate(){
        if *val == '[' {
            start_brack_index = index as i32;    
                    
        }else if *val == ']' {
            // Insert bracket
            let mut c = coeff_char_array.clone(); // digits
            let c_num:String = c.clone().into_iter().collect();

            // Convert the coeff to finite field element
            let c_fr = Fr::from(c_num.parse::<u8>().unwrap());
            let c_fr_inv = get_add_inv(c_fr);
            let c_inv_str = c_fr_inv.to_string();


            //Update c
            c.insert(0, '[');
            c.push(']');

            let coeff_string:String = c.into_iter().collect();

            //Update tracker arrays
            replace_pattern.push(coeff_string);
            replace_val.push(c_inv_str);

            //Reset bracket tracker
            start_brack_index = -1;
            coeff_char_array.clear(); //Clear

        }else{
            if start_brack_index != -1 {
                //Active neg coeff
                coeff_char_array.push(*val);
            }
        }

    }

    //Replace the updates
    // let replaced_string = op.replace(&coeff_string, &c_inv_str);
    let mut temp_op = op.to_string();
    for (pattern,val) in replace_pattern.iter().zip(replace_val){
        temp_op = temp_op.replace(pattern,&val);
    }

    temp_op
}

// Parses circuit
pub fn parse_circuit(file_name:&str) -> (Vec<HashMap<String,Vec<String>>>,Vec<String>,HashMap<String,String>) {

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
            // Parse circuit
            let replaced_string = contents.replace("\r\n", ",");
            let contraints_array_i:Vec<&str> = replaced_string.split(',').filter(|s| !s.is_empty()).collect();
            let mut parsed_constraints:Vec<String> = Vec::new();
            
            // Accomodate [-1] coeff
            for c_s in contraints_array_i.clone(){
                let neg_coeff_parsed_constraint = shield_brack_parser(c_s);
                parsed_constraints.push(neg_coeff_parsed_constraint);
            }
            shield_brack_parser("[1]a*[2]b=r1");
            
            let contraints_array :Vec<&str>= parsed_constraints.iter().map(|c|c.as_str()).collect();


            let res:Vec<&str> = contraints_array.iter().map(|val| {
                let index = val.find("*");
                
                match index {
                    Some(_) => {
                        // println!("Multiplication operators found");
                        // Validate constraint
                        let sliced_constraint = get_slice(val,"*");
                        if validate_operators(sliced_constraint,"*") == true{
                            println!("Constraint: {:?} does not follow standard",val);
                            exit(0);
                        }
                        // Extract constraint
                        let extracted_constraint_map = extract_constraints(val,"*");
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
                            match found{
                                Some(_)=> {
                                    // If operator matches
                                    if op == "+"{

                                        // println!("Addition operators found");
                                        // Validate constraint
                                        let sliced_constraint = get_slice(val,"+");
                                        if validate_operators(sliced_constraint,"+") == true{
                                            println!("Constraint: {:?} does not follow standard",val);
                                            exit(0);
                                        }

                                        let extracted_constraint_map = extract_constraints(val,"+");
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

                                        // println!("Subtraction operators found");
                                        // Validate constraint
                                        let sliced_constraint = get_slice(val,"-");
                                        if validate_operators(sliced_constraint,"-") == true{
                                            println!("Constraint: {:?} does not follow standard",val);
                                            exit(0);
                                        }

                                        let extracted_constraint_map = extract_constraints(val,"-");
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
                                        // println!("Division operators found");
                                        // Validate constraint
                                        let sliced_constraint = get_slice(val,"/");
                                        if validate_operators(sliced_constraint,"/") == true{
                                            println!("Constraint: {:?} does not follow standard",val);
                                            exit(0);
                                        }

                                        let extracted_constraint_map = extract_constraints(val,"/");
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

    let (last_out,auxillary)= out_var_list.split_last().unwrap();

    // [1,out,inputs,auxilliary]
    let solution_list_variable = [vec!["1".to_string()],vec![last_out.to_string()],input_var_list,auxillary.to_vec()].concat();

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
// Get l,r,o matrix
pub fn get_l_r_o_matrix(solution_name_list:Vec<String>,constraint_list:Vec<HashMap<String, Vec<String>>>) -> (Vec<Vec<Fr>>,Vec<Vec<Fr>>,Vec<Vec<Fr>>){
    let mut l_matrix:Vec<Vec<Fr>> = Vec::new();
    let mut r_matrix:Vec<Vec<Fr>> = Vec::new();
    let mut o_matrix:Vec<Vec<Fr>> = Vec::new();

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
    
        //Push to matrix
        l_matrix.push(solution_val_list_l);
        r_matrix.push(solution_val_list_r);
        o_matrix.push(solution_val_list_o);

    }
    (l_matrix,r_matrix,o_matrix)
}

// Compute t(x)
pub fn compute_t_poly(size:usize)-> DensePolynomial<Fp<MontBackend<FrConfig, 4>, 4>>{
    // Compute t(x) = (x-1)(x-2)..(x-n)  [Vanishing polynomial]
    let mut t_polynomial = DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]);
    for i in 1..=size{
        let rq:u8 = i.try_into().unwrap();
        let rq_poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(rq)]);
        let x_poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(0),Fr::from(1)]); // X
        let element = x_poly - rq_poly;
        t_polynomial = t_polynomial.mul(element);
    }
    t_polynomial
}

// Get polynomials 
pub fn get_polynomials(matrix:Vec<Vec<Fr>>) -> Vec<DensePolynomial<ark_ff::Fp<ark_ff::MontBackend<ark_bn254::FrConfig, 4>, 4>>>{

    // Interpolate columns 
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