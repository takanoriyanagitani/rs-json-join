use std::collections::BTreeMap;
use std::env;
use std::io::Write;
use std::process::ExitCode;

use rs_json_join::flat::mem::keystr::simple;
use rs_json_join::flat::mem::keystr::simple::{
    Larger2key, MergeJoined, MergeSmallerKeyMap, Smaller2key, SmallerRows,
};

fn sub() -> Result<(), &'static str> {
    let larger_key: String = env::var("ENV_KEY_L").ok().unwrap_or_default();
    let smaller_key: String = env::var("ENV_KEY_S").ok().unwrap_or_default();
    let smaller_map_keys: String = env::var("ENV_MAP_KEYS").ok().unwrap_or_default();
    let smaller_map_vals: String = env::var("ENV_MAP_VALS").ok().unwrap_or_default();
    let smaller_path: String = env::var("ENV_SMALLER_JSONL").ok().unwrap_or_default();
    let skeys = smaller_map_keys.split(',');
    let svals = smaller_map_vals.split(',');
    let spairs = skeys.zip(svals).map(|kv| {
        let (key, val) = kv;
        (String::from(key), String::from(val))
    });
    let smap: BTreeMap<String, String> = BTreeMap::from_iter(spairs);
    let mskm = MergeSmallerKeyMap {
        smaller_keys_map: smap,
    };

    let val2wtr = simple::val2wtr_default(); // ValueToWriter
    let val2str = simple::val2str_default(); // ValueToString

    let l2key = Larger2key::new_default(val2wtr).with_key(larger_key);
    let s2key = Smaller2key::new_default(val2str).with_key(smaller_key);
    let mut mj = MergeJoined {
        larger2key: l2key,
        smaller2key: s2key,
        merger: mskm,
    };
    let srows: SmallerRows = mj.path2smaller(smaller_path)?;
    if srows.0.is_empty() {
        return Err("empty smaller rows");
    }
    let larger_jsons = std::io::stdin();
    let joined = std::io::stdout();
    let mut locked = joined.lock();
    let _: u64 = mj.read2writer(larger_jsons.lock(), &mut locked, &srows)?;
    locked.flush().map_err(|_| "unable to flush")?;
    Ok(())
}

fn main() -> ExitCode {
    sub().map(|_| ExitCode::SUCCESS).unwrap_or_else(|e| {
        eprintln!("{e}");
        ExitCode::FAILURE
    })
}
