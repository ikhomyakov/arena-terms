use parlex::ParlexError;

/// Input encoding for the term parser.
///
/// Determines how raw input bytes are transcoded to UTF-8 when
/// the lexer produces string values (atoms, variables, strings, etc.).
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
}

impl std::fmt::Display for Encoding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Transcodes a byte slice from the given encoding to a UTF-8 string.
///
/// - [`Utf8`](Encoding::Utf8): validates as UTF-8
/// - [`Ascii`](Encoding::Ascii): validates all bytes ≤ 127
/// - [`Latin1`](Encoding::Latin1): transcodes ISO-8859-1 → UTF-8
/// - [`Windows1252`](Encoding::Windows1252): transcodes via `encoding_rs`
pub fn transcode_to_utf8(bytes: &[u8], encoding: Encoding) -> Result<String, ParlexError> {
    match encoding {
        Encoding::Utf8 => {
            let s = std::str::from_utf8(bytes)
                .map_err(|e| ParlexError::from_err(e, None))?;
            Ok(s.to_owned())
        }
        Encoding::Ascii => {
            if let Some(pos) = bytes.iter().position(|&b| b > 127) {
                return Err(ParlexError {
                    message: format!("non-ASCII byte 0x{:02X} at offset {}", bytes[pos], pos),
                    span: None,
                });
            }
            // ASCII is valid UTF-8
            Ok(unsafe { String::from_utf8_unchecked(bytes.to_vec()) })
        }
        Encoding::Latin1 => {
            let mut out = String::with_capacity(bytes.len());
            for &b in bytes {
                out.push(b as char);
            }
            Ok(out)
        }
        Encoding::Windows1252 => {
            let (cow, _, had_errors) =
                encoding_rs::WINDOWS_1252.decode(bytes);
            if had_errors {
                return Err(ParlexError {
                    message: "invalid windows-1252 sequence".to_owned(),
                    span: None,
                });
            }
            Ok(cow.into_owned())
        }
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
    fn transcode_utf8_valid() {
        let s = transcode_to_utf8("café".as_bytes(), Encoding::Utf8).unwrap();
        assert_eq!(s, "café");
    }

    #[test]
    fn transcode_utf8_invalid() {
        assert!(transcode_to_utf8(&[0xFF, 0xFE], Encoding::Utf8).is_err());
    }

    #[test]
    fn transcode_ascii_valid() {
        let s = transcode_to_utf8(b"hello", Encoding::Ascii).unwrap();
        assert_eq!(s, "hello");
    }

    #[test]
    fn transcode_ascii_invalid() {
        assert!(transcode_to_utf8(&[0x80], Encoding::Ascii).is_err());
    }

    #[test]
    fn transcode_latin1() {
        // 0xE9 = é in ISO-8859-1
        let s = transcode_to_utf8(&[0x63, 0x61, 0x66, 0xE9], Encoding::Latin1).unwrap();
        assert_eq!(s, "café");
    }

    #[test]
    fn transcode_latin1_full_range() {
        // Every byte 0x00..=0xFF is valid in Latin1
        let bytes: Vec<u8> = (0u8..=255).collect();
        let s = transcode_to_utf8(&bytes, Encoding::Latin1).unwrap();
        assert_eq!(s.chars().count(), 256);
        assert_eq!(s.chars().last(), Some('\u{FF}'));
    }

    #[test]
    fn transcode_windows1252() {
        // 0x93 = left double quote in Windows-1252 (U+201C)
        let s = transcode_to_utf8(&[0x93], Encoding::Windows1252).unwrap();
        assert_eq!(s, "\u{201C}");
    }

    #[test]
    fn name_roundtrip() {
        for enc in [Encoding::Utf8, Encoding::Ascii, Encoding::Latin1, Encoding::Windows1252] {
            assert_eq!(Encoding::from_name(enc.name()), Some(enc));
        }
    }
}
