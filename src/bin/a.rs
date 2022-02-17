#![allow(unused_imports)]
use proconio::*;

use ac_library_rs::modint::*;
use my_library_rs::hello::*;

#[fastout]
fn main() {
    use ModInt1000000007 as Mint;
    let a = Mint::new(-1);
    assert_eq!(a.val(), 1_000_000_006);

    greet();
}
