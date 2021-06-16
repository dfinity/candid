/// Hash function for [Symbolic Field Ids](https://github.com/dfinity/candid/blob/master/spec/Candid.md#shorthand-symbolic-field-ids)
#[inline]
pub fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.as_bytes().iter() {
        s = s.wrapping_mul(223).wrapping_add(*c as u32);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]

    fn test_record() {
        assert_eq!(idl_hash("name"), 1224700491);
        assert_eq!(idl_hash("street"), 288167939);
        assert_eq!(idl_hash("num"), 5496390);
        assert_eq!(idl_hash("city"), 1103114667);
        assert_eq!(idl_hash("zip"), 6090465);
    }
}
