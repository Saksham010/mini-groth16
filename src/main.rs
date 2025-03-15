use std::path::Path;
use std::fs::File;
use std::io::Read;
use std::process::exit;
use std::collections::HashMap;
use std::{rc, result, vec};
use regex::Regex;
use ark_bn254::{Fr,FqConfig,Fq2Config, G1Projective as G, G2Projective as G2};
use ark_ff::fields::Field;
use std::str::FromStr;



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
    let file: Result<File, std::io::Error> = File::open(path);
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

// Reads witness
fn create_matrix(file_name:&str){


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

    let solution_vector = vec![Fr::from(1u8),Fr::from(2u8),Fr::from(1u8),Fr::from(1u8),Fr::from(2u8),Fr::from(1u8),Fr::from(4u8),Fr::from(2u8),Fr::from(6u8),Fr::from(1u8),Fr::from(20u8),Fr::from(40u8),Fr::from(3u8),Fr::from(2u8)];

    let l_s = get_matrix_vec_mul(l_matrix.clone(),solution_vector.clone());
    let r_s = get_matrix_vec_mul(r_matrix.clone(),solution_vector.clone());
    let o_s = get_matrix_vec_mul(o_matrix.clone(),solution_vector.clone());

    println!("L*S Vector: {:?}",l_s);
    println!("R*S Vector: {:?}",r_s);
    println!("O*S Vector: {:?}",o_s);


    let t = Fr::from_str("14592161914559516814830937163504850059032242933610689562465469457717205663745").unwrap();
    let six_fr = Fr::from(6u8);
    let ans = six_fr *t;

    println!("ANS: {:?}",ans);


    // "a":"1",
    // "b":"1",
    // "r1":"20",
    // "c":"2",
    // "r2":"40",
    // "e":"1",
    // "r3":"3",
    // "f":"4",
    // "g":"2",
    // "r4":"2",
    // "h":"6",
    // "i":"1",
    // "r5":"1"


    // println!("Constraint_list: {:?}",constraint_list);
    // println!("Solution name list: {:?}",solution_name_list);

}
