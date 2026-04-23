use crate::TermError;

/// Input encoding for term data.
///
/// Determines how raw bytes are transcoded to/from UTF-8 when
/// producing or consuming string values (atoms, variables, strings, etc.).
/// Binary content (`bin{...}`) always uses raw bytes regardless of encoding.
///
/// Encoding names follow the WHATWG Encoding Standard / IANA charset names
/// (the same names accepted by `encoding_rs` and HTTP `Content-Type` headers).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Encoding {
    #[default]
    Utf8,
    Ascii,
    Latin1,
    Windows1252,
}

impl Encoding {
    /// Parses an encoding name (case-insensitive) into an [`Encoding`].
    ///
    /// Accepts WHATWG/IANA names and common aliases:
    /// - `"utf-8"`, `"utf8"` → [`Utf8`](Encoding::Utf8)
    /// - `"us-ascii"`, `"ascii"` → [`Ascii`](Encoding::Ascii)
    /// - `"iso-8859-1"`, `"latin1"`, `"latin-1"` → [`Latin1`](Encoding::Latin1)
    /// - `"windows-1252"`, `"cp1252"` → [`Windows1252`](Encoding::Windows1252)
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_ascii_lowercase().as_str() {
            "utf-8" | "utf8" => Some(Self::Utf8),
            "us-ascii" | "ascii" | "iso-ir-6" => Some(Self::Ascii),
            "iso-8859-1" | "latin1" | "latin-1" | "iso_8859-1" | "l1" => Some(Self::Latin1),
            "windows-1252" | "cp1252" | "x-cp1252" => Some(Self::Windows1252),
            _ => None,
        }
    }

    /// Returns the canonical WHATWG/IANA name for this encoding.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Utf8 => "utf-8",
            Self::Ascii => "us-ascii",
            Self::Latin1 => "iso-8859-1",
            Self::Windows1252 => "windows-1252",
        }
    }

    /// Decodes a byte slice from this encoding into a UTF-8 string.
    ///
    /// # Examples
    /// ```
    /// # use arena_terms::Encoding;
    /// let s = Encoding::Latin1.decode(&[0x63, 0x61, 0x66, 0xE9]).unwrap();
    /// assert_eq!(s, "café");
    /// ```
    pub fn decode(&self, bytes: &[u8]) -> Result<String, TermError> {
        match self {
            Self::Utf8 => {
                let s = std::str::from_utf8(bytes)
                    .map_err(|e| TermError::Encoding(e.to_string().into()))?;
                Ok(s.to_owned())
            }
            Self::Ascii => {
                if let Some(pos) = bytes.iter().position(|&b| b > 127) {
                    return Err(TermError::Encoding(
                        format!("non-ASCII byte 0x{:02X} at offset {}", bytes[pos], pos).into(),
                    ));
                }
                Ok(unsafe { String::from_utf8_unchecked(bytes.to_vec()) })
            }
            Self::Latin1 => {
                let mut out = String::with_capacity(bytes.len());
                for &b in bytes {
                    out.push(b as char);
                }
                Ok(out)
            }
            Self::Windows1252 => {
                let (cow, _, had_errors) = encoding_rs::WINDOWS_1252.decode(bytes);
                if had_errors {
                    return Err(TermError::Encoding(
                        "invalid windows-1252 sequence".into(),
                    ));
                }
                Ok(cow.into_owned())
            }
        }
    }

    /// Encodes a UTF-8 string into bytes in this encoding.
    ///
    /// # Examples
    /// ```
    /// # use arena_terms::Encoding;
    /// let bytes = Encoding::Latin1.encode("café").unwrap();
    /// assert_eq!(bytes, vec![0x63, 0x61, 0x66, 0xE9]);
    /// ```
    pub fn encode(&self, s: &str) -> Result<Vec<u8>, TermError> {
        match self {
            Self::Utf8 => Ok(s.as_bytes().to_vec()),
            Self::Ascii => {
                if let Some(ch) = s.chars().find(|c| !c.is_ascii()) {
                    return Err(TermError::Encoding(
                        format!("non-ASCII character '{}' (U+{:04X})", ch, ch as u32).into(),
                    ));
                }
                Ok(s.as_bytes().to_vec())
            }
            Self::Latin1 => {
                let mut out = Vec::with_capacity(s.len());
                for ch in s.chars() {
                    let cp = ch as u32;
                    if cp > 0xFF {
                        return Err(TermError::Encoding(
                            format!(
                                "character '{}' (U+{:04X}) not representable in ISO-8859-1",
                                ch, cp
                            )
                            .into(),
                        ));
                    }
                    out.push(cp as u8);
                }
                Ok(out)
            }
            Self::Windows1252 => {
                let (cow, _, had_errors) = encoding_rs::WINDOWS_1252.encode(s);
                if had_errors {
                    return Err(TermError::Encoding(
                        format!(
                            "string contains characters not representable in windows-1252"
                        )
                        .into(),
                    ));
                }
                Ok(cow.into_owned())
            }
        }
    }
}

impl std::fmt::Display for Encoding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_name_case_insensitive() {
        assert_eq!(Encoding::from_name("UTF-8"), Some(Encoding::Utf8));
        assert_eq!(Encoding::from_name("utf8"), Some(Encoding::Utf8));
        assert_eq!(Encoding::from_name("ISO-8859-1"), Some(Encoding::Latin1));
        assert_eq!(Encoding::from_name("latin1"), Some(Encoding::Latin1));
        assert_eq!(Encoding::from_name("Windows-1252"), Some(Encoding::Windows1252));
        assert_eq!(Encoding::from_name("us-ascii"), Some(Encoding::Ascii));
        assert_eq!(Encoding::from_name("unknown"), None);
    }

    #[test]
    fn decode_utf8_valid() {
        assert_eq!(Encoding::Utf8.decode("café".as_bytes()).unwrap(), "café");
    }

    #[test]
    fn decode_utf8_invalid() {
        assert!(Encoding::Utf8.decode(&[0xFF, 0xFE]).is_err());
    }

    #[test]
    fn decode_ascii_valid() {
        assert_eq!(Encoding::Ascii.decode(b"hello").unwrap(), "hello");
    }

    #[test]
    fn decode_ascii_invalid() {
        assert!(Encoding::Ascii.decode(&[0x80]).is_err());
    }

    #[test]
    fn decode_latin1() {
        assert_eq!(
            Encoding::Latin1.decode(&[0x63, 0x61, 0x66, 0xE9]).unwrap(),
            "café"
        );
    }

    #[test]
    fn decode_latin1_full_range() {
        let bytes: Vec<u8> = (0u8..=255).collect();
        let s = Encoding::Latin1.decode(&bytes).unwrap();
        assert_eq!(s.chars().count(), 256);
        assert_eq!(s.chars().last(), Some('\u{FF}'));
    }

    #[test]
    fn decode_windows1252() {
        // 0x93 = left double quote in Windows-1252 (U+201C)
        assert_eq!(Encoding::Windows1252.decode(&[0x93]).unwrap(), "\u{201C}");
    }

    #[test]
    fn encode_utf8() {
        assert_eq!(Encoding::Utf8.encode("café").unwrap(), "café".as_bytes());
    }

    #[test]
    fn encode_ascii_valid() {
        assert_eq!(Encoding::Ascii.encode("hello").unwrap(), b"hello");
    }

    #[test]
    fn encode_ascii_invalid() {
        assert!(Encoding::Ascii.encode("café").is_err());
    }

    #[test]
    fn encode_latin1() {
        assert_eq!(
            Encoding::Latin1.encode("café").unwrap(),
            vec![0x63, 0x61, 0x66, 0xE9]
        );
    }

    #[test]
    fn encode_latin1_out_of_range() {
        // U+0100 (Ā) is not in Latin1
        assert!(Encoding::Latin1.encode("Ā").is_err());
    }

    #[test]
    fn encode_windows1252() {
        assert_eq!(
            Encoding::Windows1252.encode("\u{201C}").unwrap(),
            vec![0x93]
        );
    }

    #[test]
    fn decode_encode_roundtrip() {
        for enc in [Encoding::Utf8, Encoding::Ascii, Encoding::Latin1, Encoding::Windows1252] {
            let original = b"hello";
            let s = enc.decode(original).unwrap();
            let bytes = enc.encode(&s).unwrap();
            assert_eq!(&bytes, original, "roundtrip failed for {}", enc);
        }
    }

    #[test]
    fn encode_decode_roundtrip_latin1() {
        let original = "café";
        let bytes = Encoding::Latin1.encode(original).unwrap();
        let s = Encoding::Latin1.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    #[test]
    fn name_roundtrip() {
        for enc in [Encoding::Utf8, Encoding::Ascii, Encoding::Latin1, Encoding::Windows1252] {
            assert_eq!(Encoding::from_name(enc.name()), Some(enc));
        }
    }
}
