use carcara::{
    benchmarking::{CollectResults, CsvBenchmarkResults, RunMeasurement},
    checker, parser, CarcaraOptions,
};
use crossbeam_queue::ArrayQueue;
use std::{
    fs::File,
    io::{self, BufReader},
    path::{Path, PathBuf},
    thread,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy)]
struct JobDescriptor<'a> {
    problem_file: &'a Path,
    proof_file: &'a Path,
    run_index: usize,
}

fn run_job<T: CollectResults + Default + Send>(
    results: &mut T,
    job: JobDescriptor,
    options: &CarcaraOptions,
    elaborate: bool,
) -> Result<bool, carcara::Error> {
    let proof_file_name = job.proof_file.to_str().unwrap();
    let mut checker_stats = checker::CheckerStatistics {
        file_name: proof_file_name,
        elaboration_time: Duration::ZERO,
        polyeq_time: Duration::ZERO,
        assume_time: Duration::ZERO,
        assume_core_time: Duration::ZERO,
        results: std::mem::take(results),
    };

    let total = Instant::now();

    let parsing = Instant::now();
    let config = parser::Config {
        apply_function_defs: options.apply_function_defs,
        expand_lets: options.expand_lets,
        allow_int_real_subtyping: options.allow_int_real_subtyping,
        allow_unary_logical_ops: !options.strict,
    };
    let (prelude, proof, mut pool, _) = parser::parse_instance(
        BufReader::new(File::open(job.problem_file)?),
        BufReader::new(File::open(job.proof_file)?),
        config,
    )?;
    let parsing = parsing.elapsed();

    let config = checker::Config::new()
        .strict(options.strict)
        .ignore_unknown_rules(options.ignore_unknown_rules)
        .lia_options(options.lia_options.clone());
    let mut checker = checker::ProofChecker::new(&mut pool, config, &prelude);

    let checking = Instant::now();

    let checking_result = if elaborate {
        checker
            .check_and_elaborate_with_stats(proof, &mut checker_stats)
            .map(|(is_holey, _)| is_holey)
    } else {
        checker.check_with_stats(&proof, &mut checker_stats)
    };
    let checking = checking.elapsed();

    let total = total.elapsed();

    checker_stats.results.add_run_measurement(
        &(proof_file_name.to_string(), job.run_index),
        RunMeasurement {
            parsing,
            checking,
            elaboration: checker_stats.elaboration_time,
            scheduling: Duration::ZERO,
            total,
            polyeq: checker_stats.polyeq_time,
            assume: checker_stats.assume_time,
            assume_core: checker_stats.assume_core_time,
        },
    );
    *results = checker_stats.results;
    checking_result
}

fn worker_thread<T: CollectResults + Default + Send>(
    jobs_queue: &ArrayQueue<JobDescriptor>,
    options: &CarcaraOptions,
    elaborate: bool,
) -> T {
    let mut results = T::default();

    while let Some(job) = jobs_queue.pop() {
        match run_job(&mut results, job, options, elaborate) {
            Ok(true) => results.register_holey(),
            Err(e) => {
                log::error!("encountered error in file '{}'", job.proof_file.display());
                results.register_error(&e);
            }
            _ => (),
        }
    }

    results
}

pub fn run_benchmark<T: CollectResults + Default + Send>(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_jobs: usize,
    options: &CarcaraOptions,
    elaborate: bool,
) -> T {
    const STACK_SIZE: usize = 128 * 1024 * 1024;

    let jobs_queue = ArrayQueue::new(instances.len() * num_runs);
    for run_index in 0..num_runs {
        for (problem, proof) in instances {
            let job = JobDescriptor {
                problem_file: problem,
                proof_file: proof,
                run_index,
            };
            jobs_queue.push(job).unwrap();
        }
    }

    thread::scope(|s| {
        let jobs_queue = &jobs_queue; // So we don't try to move the queue into the thread closure

        // We of course need to `collect` here to ensure we spawn all threads before starting to
        // `join` them
        #[allow(clippy::needless_collect)]
        let workers: Vec<_> = (0..num_jobs)
            .map(|_| {
                thread::Builder::new()
                    .stack_size(STACK_SIZE)
                    .spawn_scoped(s, move || worker_thread(jobs_queue, options, elaborate))
                    .unwrap()
            })
            .collect();

        workers
            .into_iter()
            .map(|w| w.join().unwrap())
            .reduce(T::combine)
            .unwrap()
    })
}

pub fn run_csv_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_jobs: usize,
    options: &CarcaraOptions,
    elaborate: bool,
    runs_dest: &mut dyn io::Write,
    by_rule_dest: &mut dyn io::Write,
) -> io::Result<()> {
    let result: CsvBenchmarkResults =
        run_benchmark(instances, num_runs, num_jobs, options, elaborate);
    println!(
        "{} errors encountered during benchmark",
        result.num_errors()
    );
    if result.num_errors() > 0 {
        println!("invalid");
    } else if result.is_holey() {
        println!("holey");
    } else {
        println!("valid");
    }
    result.write_csv(runs_dest, by_rule_dest)
}
