use carcara::{produce_lambdapi_proof, CarcaraOptions};
use std::fs::File;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// For all proof file in carcara/tests/problems directory,
/// we translate the Alethe proof in Lambdapi proof and save
/// content in a temporary file in directory carcara/lambdapi.
/// Then, run the command `lambdapi check` for each.
/// If the command exit with status 0 then we remove the file and the test terminate,
/// otherwise we keep the file for debugging reason and panic test.

macro_rules! test_translate {
    ($name:ident) => {
        #[test]
        fn $name() {
            // Translate the Alethe proof
            let problem_asset_dir = PathBuf::from("tests/problems/");
            let translated_proof_dir = PathBuf::from("lambdapi");

            let problem_path = problem_asset_dir
                .join((stringify!($name)))
                .with_extension("smt2");

            let proof_path = problem_asset_dir
                .join((stringify!($name)))
                .with_extension("smt2.proof");

            let problem = io::BufReader::new(
                File::open(&problem_path).expect(
                    format!(
                        "File at {} can not be opened",
                        problem_path.to_string_lossy()
                    )
                    .as_str(),
                ),
            );
            let proof = io::BufReader::new(File::open(&proof_path).expect(
                format!("File at {} can not be opened", proof_path.to_string_lossy()).as_str(),
            ));

            // Save the translated the Alethe proof in a temporary file in carcara/lambdapi directory

            let filename = problem_path
                .file_name()
                .unwrap()
                .to_string_lossy()
                .replace(".smt2", "");

            let mut options = CarcaraOptions::default();
            options.ignore_unknown_rules = true;

            let proof_translated_file =
                produce_lambdapi_proof(filename.clone(), problem, proof, options)
                    .expect("Translation failed");

            let lambdapi_proof_path = translated_proof_dir
                .join(filename.clone())
                .with_extension("lp");

            let mut lambdapi_proof_file: File = File::create(&lambdapi_proof_path)
                .expect("Could not create the translated file to write content");

            lambdapi_proof_file
                .write_all(format!("{}", proof_translated_file).as_bytes())
                .unwrap();

            // Run `lambdapi check <FILE>` command to verify the proof

            let status = Command::new("lambdapi")
                .arg("check")
                .arg("--verbose=0")
                .arg("--no-warnings")
                .arg("--timeout=5")
                .arg(&lambdapi_proof_path)
                .status()
                .expect("Could not run Lambdapi check command");

            // Remove the file if it is a success otherwise we keep it for debug reason
            if status.success() {
                //std::fs::remove_file(lambdapi_proof_path)
                //    .expect("Could not remove translated proof file");
            } else {
                panic!("Lambdapi check failed")
            }
        }
    };
}

#[cfg(test)]
mod translate {
    use super::*;

    test_translate!(step_simp_1);

    test_translate!(tlapm_c4a839);

    //test_translate!(tlapm_0ad495);

    test_translate!(tlapm_0b9140);

    test_translate!(tlapm_3cbc97);

    // FIXME: bug related to Carcara optimisation (Passed)
    // test_translate!(tlapm_9deec9);

    test_translate!(tlapm_2197e4);

    // FIXME: bug related to Carcara optimisation (Passed)
    // test_translate!(tlapm_4222fc);

    test_translate!(tlapm_4561b7);

    test_translate!(tlapm_b01e66);

    test_translate!(tlapm_c42a04);

    // FIXME: bug related to Carcara optimisation (Passed)
    //test_translate!(tlapm_e03cb1);

    test_translate!(tlapm_f52471);

    //test_translate!(tlapm_23bce6);

    //test_translate!(unsat-07-sko);

    // FIXME: bug related to Carcara optimisation (Passed)
    //test_translate!(tlapm_f84230);

    // FIXME: bug related to Carcara optimisation (Passed)
    //test_translate!(tlapm_fa32ac);

    // FIXME: bug in Carcara axion is removed (Not Pass)
    //test_translate!(tlapm_c85796);

    // FIXME: bug in Carcara checker
    // [ERROR] checking failed on step 'a25' with rule 'assume': term '(forall ((smt__a1 Idv) (smt__y1 Idv)) (=> (smt__TLA______Mem smt__y1 smt__a1) (smt__TLA______Mem (smt__TLA______FunApp smt__VARIABLE___alloc___ smt__y1) (smt__TLA______SetOf___1___flatnd___1 smt__a1))))' was not in original problem's assumptions
    //test_translate!(tlapm_a0df54);
}
