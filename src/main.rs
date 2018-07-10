extern crate wasm_reloc_analysis as ra;

fn main() -> Result<(), Box<std::error::Error>>{
    ra::run_reloc_analysis()

}
