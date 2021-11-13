#![no_main]

use std::io::{self, Write};

fn fuzz_with(data: &str) {
    if data
        .strip_prefix("_R")
        .map_or(false, |rest| rest.bytes().all(|c| c.is_ascii_graphic()))
    {
        let mut sink = io::sink();

        if let Ok(symbol) = rustc_demangle::try_demangle(data) {
            let _ = write!(sink, "{}", symbol);
            let _ = write!(sink, "{:#}", symbol);
        }
    }
}

libfuzzer_sys::fuzz_target!(|data: &str| {
    fuzz_with(data);
});