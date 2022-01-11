use clap::{AppSettings, Parser};
use std::fs::File;
use std::io::{BufRead, BufReader};

#[derive(Parser)]
#[clap(author, version, about)]
#[clap(global_setting(AppSettings::PropagateVersion))]
#[clap(global_setting(AppSettings::UseLongFormatForHelpSubcommand))]
struct Cli {
    #[clap(long, short = 'r')]
    /// Only translate reserved rvv instructions.
    reserved_only: bool,

    /// The original assembly source file path.
    asm_file: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    let origin_asm_file = File::open(cli.asm_file)?;
    for result_line in BufReader::new(origin_asm_file).lines() {
        let line = result_line?;
        if let Ok(Some(code)) = rvv_encode::encode(line.as_str(), cli.reserved_only) {
            let indent = line.chars().take_while(|c| c == &' ').collect::<String>();
            let [b0, b1, b2, b3] = code.to_le_bytes();
            println!(
                "{}.byte {:#04x}, {:#04x}, {:#04x}, {:#04x} ; {}",
                indent,
                b0,
                b1,
                b2,
                b3,
                line.trim(),
            );
        } else {
            println!("{}", line);
        }
    }
    Ok(())
}
