use std::time::{Instant, SystemTime};

use anyhow::{bail, Result};

use crate::value::Value;

pub fn clock(args: &[Value]) -> Result<Value> {
    if args.len() != 0 {
        bail!("arity: expected 0 arguments");
    }
    Ok(Value::Number(
        SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs_f64(),
    ))
}
