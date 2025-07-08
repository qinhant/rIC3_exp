use log::{trace};
use once_cell::sync::OnceCell;
use std::collections::BTreeMap as Map;
use std::fmt::Debug;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::sync::RwLock;
use std::path::Path;

#[derive(Clone, Debug)]
pub struct RelationData {
    pub entries: Vec<[i64; 4]>, // original rows as signed integers
    pub sym_map: Map<i64, i64>,    // symmetry map
    pub equiv_map: Map<i64, i64>,  // equivalence predicate map
    pub eqinit_map: Map<i64, i64>,  // eqinit predicate map
}

impl RelationData {
    pub fn init_relation_data<P: AsRef<std::path::Path>>(path: P, input_count: usize, latch_count: usize) {
        let data = RelationData::from_file(path, input_count, latch_count).expect("Failed to load RelationData");
        RELATION_DATA.set(RwLock::new(data)).ok();
    }

    pub fn get_relation_data() -> std::sync::RwLockReadGuard<'static, RelationData> {
        RELATION_DATA
            .get()
            .expect("RelationData not initialized")
            .read()
            .unwrap()
    }

    pub fn from_file<P: AsRef<std::path::Path>>(path: P, input_count: usize, latch_count: usize) -> std::io::Result<Self> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
    
        let mut entries = Vec::new();
        let mut sym_map = Map::new();
        let mut equiv_map = Map::new();
        let mut eqinit_map = Map::new();
        
        for (line_num, line) in reader.lines().enumerate() {
            let line: String = line?;
            if line_num == 0 {
                continue; // Skip header
            }
    
            let fields: Vec<&str> = line.split_whitespace().collect();
            if fields.len() < 4 {
                eprintln!("Warning: line {} has fewer than 4 fields", line_num + 1);
                continue;
            }
    
            let f0 = fields[0].parse::<i64>().unwrap_or(0) + input_count as i64 + 1;
            let f1 = fields[1].parse::<i64>().unwrap_or(0) + input_count as i64 + 1;
            let f2 = match fields[2].parse::<i64>().unwrap_or(0) {
                -1 => -1, // If the field is 0, we keep it as 0
                v => v + input_count as i64 + 1, // Otherwise, adjust by input_count
            };
            let f3 = match fields[3].parse::<i64>().unwrap_or(0) {
                -1 => -1,
                v => v + input_count as i64 + 1,
            };

            let entry = [f0, f1, f2, f3];
            entries.push(entry);
    
            sym_map.insert(f0, f1);
            equiv_map.insert(f0, f2);
            eqinit_map.insert(f0, f3);
        }

        Ok(RelationData { entries, sym_map, equiv_map, eqinit_map })
    }

    pub fn get(&self, index: usize) -> Option<&[i64; 4]> {
        self.entries.get(index)
    }

    /// Get value from map1 (field0 → field1)
    pub fn get_sym_var(&self, key: i64) -> Option<i64> {
        self.sym_map.get(&key).copied()
    }

    /// Get value from map2 (field0 → field2)
    pub fn get_equiv_predicate(&self, key: i64) -> Option<i64> {
        self.equiv_map.get(&key).copied()
    }

    /// Get value from map3 (field0 → field3)
    pub fn get_eqinit_predicate(&self, key: i64) -> Option<i64> {
        self.eqinit_map.get(&key).copied()
    }


}

static RELATION_DATA: OnceCell<RwLock<RelationData>> = OnceCell::new();