use clap::Parser;

#[derive(Parser)]
struct Args {
    /// Path to BASE
    base_path: std::path::PathBuf,

    /// Path to OTHER
    other_path: std::path::PathBuf,

    /// Pathj to THIS
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

    let base = std::fs::read_to_string(&args.base_path).unwrap();
    let base_lines = base.split_inclusive('\n').collect::<Vec<_>>();
    let other = std::fs::read_to_string(&args.other_path).unwrap();
    let other_lines = other.split_inclusive('\n').collect::<Vec<_>>();
    let this = std::fs::read_to_string(&args.this_path).unwrap();
    let this_lines = this.split_inclusive('\n').collect::<Vec<_>>();

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
