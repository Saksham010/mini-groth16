use std::path::Path;
use std::fs::File;
use std::io::Read;

/*
Parses the circuit 
*/
fn parse_circuit(file_name:&str){
    let path = Path::new(file_name);
    let file: Result<File, std::io::Error> = File::open(path);
    let mut contents = String::new();
    let res = file.expect("Unable to open").read_to_string(&mut contents);
    let mut shield_brack: bool = false;
    let mut parsed_operations: Vec<[String; 5]> = Vec::new();

    //Handle error
    match res {
        Ok(_) => {
            println!("Analyzing circuit");
        }
        Err(_) => {
            panic!("Circuit analysis failed");
        }
    }

}