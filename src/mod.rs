#![feature(macro_rules, managed_boxes, default_type_params, phase, globs)]

pub use set::HashSet;
pub use map::HashMap;
pub use map::Entries;
pub use map::MoveEntries;
pub use map::INITIAL_CAPACITY;

mod bench;
mod hit;
mod map;
mod set;

fn main() { }

