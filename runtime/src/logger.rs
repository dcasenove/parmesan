use bincode::{deserialize_from, serialize_into};
use std::{collections::HashMap, env, fs, io, path::Path, vec::Vec};

use crate::{len_label, tag_set_wrap};
use angora_common::{cond_stmt_base::CondStmtBase, config, defs, log_data::LogData};

#[derive(Debug)]
pub struct Logger {
    data: LogData,
    fd: Option<fs::File>,
    paths: Vec<u32>,
    order_map: HashMap<(u32, u32), u32>,
}

impl Logger {
    pub fn new() -> Self {
        // export ANGORA_TRACK_OUTPUT=track.log
        let fd = match env::var(defs::TRACK_OUTPUT_VAR) {
            Ok(path) => match fs::File::create(&path) {
                Ok(f) => Some(f),
                Err(_) => None,
            },
            Err(_) => None,
        };

        let npaths = match env::var(defs::NPATHS){
            Ok(npaths) => npaths.parse().unwrap(),
            Err(_) => 0,
        };
        let mut paths: Vec<u32> = Vec::new();
        for i in 0..npaths {
            let mut path = env::var(["PATH_TO_TARGET".to_string(), i.to_string()].join(" ").to_string()).unwrap();
            paths.append(&mut path.split_whitespace().map(|s| s.parse().expect("parse error")).collect::<Vec<u32>>());
        }

        Self {
            data: LogData::new(),
            fd,
            paths,
            order_map: HashMap::new(),
        }
    }

    fn save_tag(&mut self, lb: u32) {
        if lb > 0 {
            let tag = tag_set_wrap::tag_set_find(lb as usize);
            self.data.tags.entry(lb).or_insert(tag);
        }
    }

    pub fn save_magic_bytes(&mut self, bytes: (Vec<u8>, Vec<u8>)) {
        let i = self.data.cond_list.len();
        if i > 0 {
            self.data.magic_bytes.insert(i - 1, bytes);
        }
    }

    pub fn save_ind(&mut self, indirect_edge: (u32, u32)) {
        self.data.ind_edges.push(indirect_edge);
    }

    // like the fn in fparser.rs
    pub fn get_order(&mut self, cond: &mut CondStmtBase) -> u32 {
        let order_key = (cond.cmpid, cond.context);
        let order = self.order_map.entry(order_key).or_insert(0);
        if cond.order == 0 {
            // first case in switch
            let order_inc = *order + 1;
            *order = order_inc;
        }
        cond.order += *order;
        *order
    }

    pub fn save(&mut self, mut cond: CondStmtBase) {
        if cond.lb1 == 0 && cond.lb2 == 0 {
            return;
        }

        let mut order = 0;

        // also modify cond to remove len_label information
        let len_cond = len_label::get_len_cond(&mut cond);

        if cond.op < defs::COND_AFL_OP || cond.op == defs::COND_FN_OP {
            order = self.get_order(&mut cond);
        }
        if order <= config::MAX_COND_ORDER {
            self.save_tag(cond.lb1);
            self.save_tag(cond.lb2);
            self.data.cond_list.push(cond);

            if let Some(mut c) = len_cond {
                c.order = 0x10000 + order; // avoid the same as cond;
                self.data.cond_list.push(c);
            }
        }
    }

    pub fn untainted_save(&mut self, cond: CondStmtBase) {
        if self.paths.contains(&cond.cmpid) {
            self.data.untainted_cond_list.push(cond);
        }
    }

    fn fini(&self) {
        if let Some(fd) = &self.fd {
            let mut writer = io::BufWriter::new(fd);
            serialize_into(&mut writer, &self.data).expect("Could not serialize data.");
        }
    }
}

impl Drop for Logger {
    fn drop(&mut self) {
        self.fini();
    }
}

pub fn get_log_data(path: &Path) -> io::Result<LogData> {
    let f = fs::File::open(path)?;
    if f.metadata().unwrap().len() == 0 {
        return Err(io::Error::new(io::ErrorKind::Other, "Could not find any interesting constraint!, Please make sure taint tracking works or running program correctly."));
    }
    let mut reader = io::BufReader::new(f);
    match deserialize_from::<&mut io::BufReader<fs::File>, LogData>(&mut reader) {
        Ok(v) => Ok(v),
        Err(_) => Err(io::Error::new(io::ErrorKind::Other, "bincode parse error!")),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
