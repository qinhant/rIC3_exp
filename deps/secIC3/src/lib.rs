use log::{trace};
use once_cell::sync::OnceCell;
use std::collections::BTreeMap as Map;
use std::fmt::Debug;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::sync::RwLock;
use std::path::Path;

#[derive(Clone)]
#[derive(Debug)]
pub struct RelationData {
    pub entries: Vec<[f64; 4]>, // or Vec<MyEntry>
}

impl RelationData {
    pub fn init_relation_data<P: AsRef<std::path::Path>>(path: P) {
        let data = RelationData::from_file(path).expect("Failed to load RelationData");
        RELATION_DATA.set(RwLock::new(data)).ok();
    }

    pub fn get_relation_data() -> std::sync::RwLockReadGuard<'static, RelationData> {
        RELATION_DATA
            .get()
            .expect("RelationData not initialized")
            .read()
            .unwrap()
    }

    pub fn from_file<P: AsRef<std::path::Path>>(path: P) -> std::io::Result<Self> {
        use std::io::{BufRead, BufReader};
        let file = std::fs::File::open(path)?;
        let reader = BufReader::new(file);

        let mut entries = Vec::new();

        for (line_num, line) in reader.lines().enumerate() {
            let line = line?;
            if line_num == 0 {
                continue; // Skip header
            }

            let fields: Vec<&str> = line.split_whitespace().collect();
            if fields.len() < 4 {
                eprintln!("Warning: line {} has fewer than 4 fields", line_num + 1);
                continue;
            }

            let entry = [
                fields[0].parse::<f64>().unwrap_or(0.0),
                fields[1].parse::<f64>().unwrap_or(0.0),
                fields[2].parse::<f64>().unwrap_or(0.0),
                fields[3].parse::<f64>().unwrap_or(0.0),
            ];
            entries.push(entry);
        }

        Ok(RelationData { entries })
    }

    pub fn get(&self, index: usize) -> Option<&[f64; 4]> {
        self.entries.get(index)
    }
}

static RELATION_DATA: OnceCell<RwLock<RelationData>> = OnceCell::new();