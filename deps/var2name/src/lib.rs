use log::{trace};
use once_cell::sync::OnceCell;
use core::panic;
use std::collections::BTreeMap as Map;
use std::fmt::Debug;
use std::fs::File;
use std::io::BufRead;
use std::sync::RwLock;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarType {
    Input,
    Latch,
    Wire,
}

impl VarType {
    fn from_str(s: &str) -> Self {
        match s {
            "input" => VarType::Input,
            "latch" => VarType::Latch,
            "invlatch" => VarType::Latch, // treat invlatch as latch
            "wire" => VarType::Wire,
            _ => panic!("Unknown variable type: {}", s),
        }
    }
}

#[derive(Clone)]
pub struct VarInfo {
    pub node_type: VarType,
    pub id: usize,
    pub index: usize,
    pub name: String,
    pub is_vector: bool,
}

impl Debug for VarInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_vector || self.index > 0 {
            write!(f, "{}[{}]", self.name, self.index)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

pub struct Var2Name {
    vars: Map<usize, VarInfo>,
    refine_inv: Map<usize, usize>, // from current id to original id
    refine: Map<usize, usize>, // from original id to current id
    input_count: usize,
    latch_count: usize,
}

impl Var2Name {
    fn flush_is_vector(vars: &mut Map<usize, VarInfo>) {
        let mut cnt = Map::<String, usize>::new();
        for (_, var) in vars.iter() {
            let count = cnt.entry(var.name.clone()).or_insert(0);
            *count += 1;
        }
        for (_, var) in vars.iter_mut() {
            if let Some(count) = cnt.get(&var.name) {
                var.is_vector = *count > 1;
            }
        }
    }

    fn get_num_of_input_latch(filename: &str) -> (usize, usize) {
        let file = File::open(filename).unwrap();
        let mut reader = std::io::BufReader::new(file);
        let mut line = String::new();
        reader.read_line(&mut line).unwrap();
        let parts: Vec<&str> = line.trim().split_whitespace().collect();
        assert!(parts.len() >= 6, "Invalid first line format: {}", line);
        let input_count = parts[2].parse::<usize>().unwrap();
        let latch_count = parts[3].parse::<usize>().unwrap();
        return (input_count, latch_count);
    }

    fn collect_vars(map_filename: &str) -> Vec<VarInfo> {
        let mut vars = Vec::new();
        let file = File::open(map_filename).unwrap();
        let mut reader = std::io::BufReader::new(file);
        let mut line = String::new();
        while reader.read_line(&mut line).unwrap() > 0 {
            let parts: Vec<&str> = line.trim().split_whitespace().collect();
            assert!(parts.len() == 4, "Invalid line format: {}", line);
            vars.push(VarInfo {
                node_type: VarType::from_str(&parts[0].to_string()),
                id: parts[1].parse().unwrap(),
                index: parts[2].parse().unwrap(),
                name: parts[3].to_string(),
                is_vector: false,
            });
            line.clear();
        }
        return vars;
    }

    pub fn new(map_filename: &str, aig_filename: &str) -> Self {
        let (input_count, latch_count) = Self::get_num_of_input_latch(aig_filename);
        println!(
            "Input count: {}, Latch count: {}",
            input_count, latch_count
        );
        let vars_vec = Self::collect_vars(map_filename);
        let calc_node_id = |var: &VarInfo| match var.node_type {
            VarType::Input => 1 + var.id,
            VarType::Latch => 1 + input_count + var.id,
            VarType::Wire => 1 + input_count + latch_count + var.id,
        };
        let mut vars_map: Map<usize, VarInfo> = Map::new();
        for var in vars_vec {
            let id = calc_node_id(&var);
            match vars_map.get_mut(&id) {
                None => {
                    vars_map.insert(id, var);
                }
                Some(existing_var) => {
                    // Keep the shorter name
                    if existing_var.name.len() > var.name.len() {
                        existing_var.name = var.name;
                    }
                }
            }
        }
        Self::flush_is_vector(&mut vars_map);
        trace!("VarMaps: {:?}", vars_map);
        return Var2Name {
            vars: vars_map,
            refine_inv: Map::new(),
            refine: Map::new(),
            input_count: input_count,
            latch_count: latch_count,
        };
    }
    pub fn get_varinfo(&self, mut id: usize) -> Option<&VarInfo> {
        // Step 1: Map refined ID back to original ID
        if let Some(&original_id) = self.refine_inv.get(&id) {
            id = original_id;
        }
    
        // Step 2: Return the full VarInfo if it exists
        self.vars.get(&id)
    }
    pub fn get_name(&self, mut id: usize) -> String {
        match self.refine_inv.get(&id) {
            None => {
                // warn!("refine inv not found for id {}", id);
                return format!("<{}>", id);
            }
            Some(&original_id) => id = original_id,
        }
        match self.vars.get(&id) {
            None => {
                // warn!("Variable ID {} not found in var2name map", id);
                return format!("{}", id);
            }
            Some(var_info) => return format!("{:?}", var_info),
        }
    }
    pub fn get(&self, mut id: usize) -> Option<VarInfo> {
        match self.refine_inv.get(&id) {
            None => {
                // warn!("refine inv not found for id {}", id);
                return None;
            }
            Some(&original_id) => id = original_id,
        }
        match self.vars.get(&id) {
            None => {
                // warn!("Variable ID {} not found in var2name map", id);
                return None;
            }
            Some(var_info) => return Some(var_info.clone()),
        }
    }

    pub fn new2origin(&self, id: usize) -> Option<usize> {
        match self.refine_inv.get(&id) {
            None => {
                // warn!("refine inv not found for id {}", id);
                return None;
            }
            Some(&origin_id) => return Some(origin_id),
        }
    }

    pub fn origin2new(&self, mut id: usize) -> Option<usize> {
        match self.refine.get(&id) {
            None => {
                // warn!("refine inv not found for id {}", id);
                return None;
            }
            Some(&new_id) => return Some(new_id),
        }
    }

    pub fn update_refine_map(&mut self, new_rst: &Map<usize, usize>) {
        let mut new_refine_inv: Map<usize, usize> = Map::new();

        for (new_id, old_id) in new_rst.iter() {
            if let Some(original_id) = self.new2origin(*old_id) {
                new_refine_inv.insert(*new_id, original_id);
            }
            else {
                panic!("Original id not found in refine_inv for old_id: {}", old_id);
            }
        }

        self.refine_inv = new_refine_inv;
        self.refine = self.refine_inv.iter().map(|(k, v)| (*v, *k)).collect();
    }
}

static _VAR2NAME: OnceCell<RwLock<Var2Name>> = OnceCell::new();

pub fn init_var2name(map_filename: &str, aig_filename: &str) {
    let _ = _VAR2NAME.set(RwLock::new(Var2Name::new(map_filename, aig_filename)));
}
pub fn init_var2name_refine_inv(refine_inv: Map<usize, usize>, refine: Map<usize, usize>) {
    trace!(
        "Initialized var2name with refine inversions {:?}",
        refine_inv
    );
    _VAR2NAME.get().unwrap().write().unwrap().refine_inv = refine_inv;
    _VAR2NAME.get().unwrap().write().unwrap().refine = refine;
}

pub fn get_origin_id(var: usize) -> Option<usize> {
    return match _VAR2NAME.get() {
        Some(var2name) => var2name.read().unwrap().refine_inv.get(&var).cloned(),
        None => None,
    };
}

pub fn get_new_id(var: usize) -> Option<usize> {
    return match _VAR2NAME.get() {
        Some(var2name) => var2name.read().unwrap().refine.get(&var).cloned(),
        None => None,
    };
}

pub fn var2name(var: usize) -> String {
    return match _VAR2NAME.get() {
        Some(var2name) => var2name.read().unwrap().get_name(var),
        None => var.to_string(),
    };
}

pub fn var2info(var: usize) -> Option<VarInfo> {
    return match _VAR2NAME.get() {
        Some(var2name) => var2name.read().unwrap().get(var),
        None => None,
    };
}

pub fn get_inputcount() -> usize {
    return match _VAR2NAME.get() {
        Some(var2name) => var2name.read().unwrap().input_count,
        None => 0,
    };
}

pub fn get_latchcount() -> usize {
    return match _VAR2NAME.get() {
        Some(var2name) => var2name.read().unwrap().latch_count,
        None => 0,
    };
}

pub fn update_var2name_refine_map(new_rst: &Map<usize, usize>) {
    _VAR2NAME
        .get()
        .unwrap()
        .write()
        .unwrap()
        .update_refine_map(new_rst);
}