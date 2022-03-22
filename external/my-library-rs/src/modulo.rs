pub trait Modulus {
    const VALUE: u32;
    const PRIMITIVE_ROOT: u32;
    const BASE: [u32; 30];
    const ROT: [u32; 30];
    const INV_ROT: [u32; 30];
    fn mul(a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        ((a as u64 * b as u64) % Self::VALUE as u64) as u32
    }
    fn add(mut a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        a += b;
        if a >= Self::VALUE {
            a -= Self::VALUE;
        }
        a
    }
    fn neg(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        if a == 0 {
            0
        } else {
            Self::VALUE - a
        }
    }
    fn sub(mut a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        a += Self::VALUE - b;
        if a >= Self::VALUE {
            a -= Self::VALUE;
        }
        a
    }
    fn pow(mut a: u32, mut n: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        let mut r = 1;
        while n > 0 {
            if n & 1 == 1 {
                r = Self::mul(r, a);
            }
            a = Self::mul(a, a);
            n >>= 1;
        }
        r
    }
    fn inv(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        Self::pow(a, Self::VALUE - 2)
    }
    fn div2(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        (a + (a & 1) * Self::VALUE) >> 1
    }
}

pub struct Mod998244353 {}
impl Modulus for Mod998244353 {
    const VALUE: u32 = 998244353;
    const PRIMITIVE_ROOT: u32 = 3;
    const BASE: [u32; 30] = [
        1, 998244352, 911660635, 372528824, 929031873, 452798380, 922799308, 781712469, 476477967,
        166035806, 258648936, 584193783, 63912897, 350007156, 666702199, 968855178, 629671588,
        24514907, 996173970, 363395222, 565042129, 733596141, 267099868, 15311432, 0, 0, 0, 0, 0,
        0,
    ];
    // root = pow(3, (998244353-1) >> 23)
    // BASE[0] = pow(root, 1<<23);
    // BASE[1] = pow(root, 1<<22);
    // ...
    // BASE[23] = pow(root, 1<<0);
    const ROT: [u32; 30] = [
        911660635, 509520358, 369330050, 332049552, 983190778, 123842337, 238493703, 975955924,
        603855026, 856644456, 131300601, 842657263, 730768835, 942482514, 806263778, 151565301,
        510815449, 503497456, 743006876, 741047443, 56250497, 867605899, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    // ROT[0] = pow(root, 1<<21)
    // ROT[1] = pow(root, (1<<20) - (1<<21))
    // ...
    // ROT[21] = pow(root, (1<<0) - (1<<1) - ... - (1<<21))
    const INV_ROT: [u32; 30] = [
        86583718, 372528824, 373294451, 645684063, 112220581, 692852209, 155456985, 797128860,
        90816748, 860285882, 927414960, 354738543, 109331171, 293255632, 535113200, 308540755,
        121186627, 608385704, 438932459, 359477183, 824071951, 103369235, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    // INV_ROT[i] * ROT[i] = 1, 0 <= i <= 21
}
