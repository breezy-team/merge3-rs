use clap::Parser;
use std::process;

#[derive(Parser)]
struct Args {
    /// Path to BASE
    base_path: std::path::PathBuf,

    /// Path to OTHER
    other_path: std::path::PathBuf,

    /// Path to THIS
    this_path: std::path::PathBuf,

    #[cfg(feature = "patiencediff")]
    /// Use patiencediff for smaller diffs
    #[clap(long, short)]
    patiencediff: bool,

    /// Reprocess results
    #[clap(long, short)]
    reprocess: bool,
}

fn main() {
    let args = Args::parse();

    let base = match std::fs::read_to_string(&args.base_path) {
        Ok(content) => content,
        Err(e) => {
            eprintln!(
                "Error reading base file '{}': {}",
                args.base_path.display(),
                e
            );
            process::exit(1);
        }
    };
    let base_lines = base.split_inclusive('\n').collect::<Vec<_>>();

    let other = match std::fs::read_to_string(&args.other_path) {
        Ok(content) => content,
        Err(e) => {
            eprintln!(
                "Error reading other file '{}': {}",
                args.other_path.display(),
                e
            );
            process::exit(1);
        }
    };
    let other_lines = other.split_inclusive('\n').collect::<Vec<_>>();

    let this = match std::fs::read_to_string(&args.this_path) {
        Ok(content) => content,
        Err(e) => {
            eprintln!(
                "Error reading this file '{}': {}",
                args.this_path.display(),
                e
            );
            process::exit(1);
        }
    };
    let this_lines = this.split_inclusive('\n').collect::<Vec<_>>();

    #[cfg(feature = "patiencediff")]
    let m3 = {
        if args.patiencediff {
            merge3::Merge3::with_patience_diff(
                base_lines.as_slice(),
                other_lines.as_slice(),
                this_lines.as_slice(),
            )
        } else {
            merge3::Merge3::new(
                base_lines.as_slice(),
                other_lines.as_slice(),
                this_lines.as_slice(),
            )
        }
    };

    #[cfg(not(feature = "patiencediff"))]
    let m3 = merge3::Merge3::new(
        base_lines.as_slice(),
        other_lines.as_slice(),
        this_lines.as_slice(),
    );

    let other_name = args.other_path.display().to_string();
    let this_name = args.this_path.display().to_string();

    for line in m3.merge_lines(
        args.reprocess,
        &merge3::StandardMarkers::new(Some(&other_name), Some(&this_name)),
    ) {
        print!("{}", line);
    }
}
