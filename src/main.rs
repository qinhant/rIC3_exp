#![feature(ptr_metadata)]

use clap::Parser;
use log::info;
use rIC3::{
    Engine,
    bmc::BMC,
    frontend::aig::AigFrontend,
    ic3::IC3,
    kind::Kind,
    options::{self, Options},
    portfolio::portfolio_main,
};
use std::{
    collections::BTreeMap,
    env, fs,
    mem::{self, transmute},
    process::exit,
    ptr,
};
use secIC3::RelationData;

fn main() {
    if env::var("RUST_LOG").is_err() {
        unsafe { env::set_var("RUST_LOG", "info") };
    }
    procspawn::init();
    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .init();
    fs::create_dir_all("/tmp/rIC3").unwrap();
    let mut options = Options::parse();
    options.model = options.model.canonicalize().unwrap();
    info!("the model to be checked: {}", options.model.display());
    if let options::Engine::Portfolio = options.engine {
        portfolio_main(options);
        unreachable!();
    }
    let mut aig = match options.model.extension() {
        Some(ext) if (ext == "btor") | (ext == "btor2") => panic!(
            "Error: rIC3 currently does not support parsing BTOR2 files. Please use btor2aiger (https://github.com/hwmcc/btor2tools) to first convert them to AIG format."
        ),
        Some(ext) if (ext == "aig") | (ext == "aag") => AigFrontend::new(&options),
        _ => panic!("Error: unsupported file format"),
    };
    let ts = aig.ts();
    // for (k, v) in ts.rst.iter() {
    //     println!("new to origin: {:?} -> {:?}", k,  v);
    // }

    if options.preprocess.sec {
        panic!("Error: sec not support");
    }
    if let Some(ref map_file) = options.model_map {
        var2name::init_var2name(map_file, options.model.to_str().unwrap());
        var2name::init_var2name_refine_inv(BTreeMap::from_iter(
            ts.rst.iter().map(|(k, v)| (k.0 as usize, v.0 as usize)),
        ),
        BTreeMap::from_iter(
            ts.rst.iter().map(|(k, v)| (v.0 as usize, k.0 as usize)),
        ));
    }

    if let Some(ref relation_file) = options.relation_file {
        RelationData::init_relation_data(relation_file, var2name::get_inputcount(), var2name::get_latchcount());
        let data = RelationData::get_relation_data();
        println!(
            "✅ RelationData initialized: {} rows loaded",
            data.entries.len()
        );
        for (i, entry) in data.entries.iter().take(5).enumerate() {
            println!("Row {}: {:?}", i, entry);
        }
    }

    // for (k, v) in ts.rst.iter() {
    //     println!("new to origin: {:?} -> {:?} {:?}", k, v, var2name::var2info(k.0 as usize));
    // }
    // for (k, v) in ts.oldtonew.iter() {
    //     println!("origin to new: {:?} {:?} -> {:?}", k, var2name::var2name(v.0 as usize), v);
    // }
    
    let mut engine: Box<dyn Engine> = match options.engine {
        options::Engine::IC3 => Box::new(IC3::new(options.clone(), ts, vec![])),
        options::Engine::Kind => Box::new(Kind::new(options.clone(), ts)),
        options::Engine::BMC => Box::new(BMC::new(options.clone(), ts)),
        _ => unreachable!(),
    };
    if options.interrupt_statistic {
        let e: (usize, usize) =
            unsafe { transmute((engine.as_mut() as *mut dyn Engine).to_raw_parts()) };
        let _ = ctrlc::set_handler(move || {
            let e: *mut dyn Engine = unsafe {
                ptr::from_raw_parts_mut(
                    e.0 as *mut (),
                    transmute::<usize, std::ptr::DynMetadata<dyn rIC3::Engine>>(e.1),
                )
            };
            let e = unsafe { &mut *e };
            e.statistic();
            exit(124);
        });
    }
    let res = engine.check();
    engine.statistic();
    match res {
        Some(true) => {
            println!("result: safe");
            if options.witness {
                println!("0");
            }
            aig.certificate(&mut engine, true)
        }
        Some(false) => {
            println!("result: unsafe");
            aig.certificate(&mut engine, false)
        }
        _ => {
            println!("result: unknown");
            if options.witness {
                println!("2");
            }
        }
    }
    mem::forget(engine);
    if let Some(res) = res {
        exit(if res { 20 } else { 10 })
    } else {
        exit(30)
    }
}
