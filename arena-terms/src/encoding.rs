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
    Iso8859_1,
    // Western
    Windows1252,
    Iso8859_15,
    Macintosh,
    // Central European
    Iso8859_2,
    Windows1250,
    // South European / Turkish
    Iso8859_3,
    Iso8859_9,
    Windows1254,
    // North European / Baltic
    Iso8859_4,
    Iso8859_10,
    Iso8859_13,
    Windows1257,
    // Celtic
    Iso8859_14,
    // Romanian
    Iso8859_16,
    // Cyrillic
    Iso8859_5,
    Windows1251,
    Koi8R,
    Koi8U,
    Ibm866,
    XMacCyrillic,
    // Greek
    Iso8859_7,
    Windows1253,
    // Hebrew
    Iso8859_8,
    Iso8859_8I,
    Windows1255,
    // Arabic
    Iso8859_6,
    Windows1256,
    // Vietnamese
    Windows1258,
    // Thai
    Windows874,
    // Japanese
    ShiftJis,
    EucJp,
    Iso2022Jp,
    // Chinese
    Gbk,
    Gb18030,
    Big5,
    // Korean
    EucKr,
    // Unicode
    Utf16Be,
    Utf16Le,
}

impl Encoding {
    /// Parses an encoding name (case-insensitive) into an [`Encoding`].
    ///
    /// Accepts WHATWG/IANA names and common aliases as recognized by
    /// `encoding_rs::Encoding::for_label()`, plus `"ascii"` and `"latin1"`.
    pub fn from_name(name: &str) -> Option<Self> {
        let lower = name.trim().to_ascii_lowercase();
        match lower.as_str() {
            "utf-8" | "utf8" => Some(Self::Utf8),
            "us-ascii" | "ascii" | "iso-ir-6" => Some(Self::Ascii),
            "iso-8859-1" | "latin1" | "latin-1" | "iso_8859-1" | "l1" => Some(Self::Iso8859_1),
            _ => {
                let enc_rs = encoding_rs::Encoding::for_label(lower.as_bytes())?;
                Self::from_encoding_rs(enc_rs)
            }
        }
    }

    /// Returns the canonical WHATWG/IANA name for this encoding.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Utf8 => "utf-8",
            Self::Ascii => "us-ascii",
            Self::Iso8859_1 => "iso-8859-1",
            _ => self.to_encoding_rs().name(),
        }
    }

    /// Returns the `encoding_rs::Encoding` for variants that delegate to it.
    fn to_encoding_rs(&self) -> &'static encoding_rs::Encoding {
        match self {
            Self::Utf8 => encoding_rs::UTF_8,
            Self::Ascii | Self::Iso8859_1 => encoding_rs::WINDOWS_1252,
            Self::Windows1252 => encoding_rs::WINDOWS_1252,
            Self::Iso8859_15 => encoding_rs::ISO_8859_15,
            Self::Macintosh => encoding_rs::MACINTOSH,
            Self::Iso8859_2 => encoding_rs::ISO_8859_2,
            Self::Windows1250 => encoding_rs::WINDOWS_1250,
            Self::Iso8859_3 => encoding_rs::ISO_8859_3,
            Self::Iso8859_9 => encoding_rs::WINDOWS_1254,
            Self::Windows1254 => encoding_rs::WINDOWS_1254,
            Self::Iso8859_4 => encoding_rs::ISO_8859_4,
            Self::Iso8859_10 => encoding_rs::ISO_8859_10,
            Self::Iso8859_13 => encoding_rs::ISO_8859_13,
            Self::Windows1257 => encoding_rs::WINDOWS_1257,
            Self::Iso8859_14 => encoding_rs::ISO_8859_14,
            Self::Iso8859_16 => encoding_rs::ISO_8859_16,
            Self::Iso8859_5 => encoding_rs::ISO_8859_5,
            Self::Windows1251 => encoding_rs::WINDOWS_1251,
            Self::Koi8R => encoding_rs::KOI8_R,
            Self::Koi8U => encoding_rs::KOI8_U,
            Self::Ibm866 => encoding_rs::IBM866,
            Self::XMacCyrillic => encoding_rs::X_MAC_CYRILLIC,
            Self::Iso8859_7 => encoding_rs::ISO_8859_7,
            Self::Windows1253 => encoding_rs::WINDOWS_1253,
            Self::Iso8859_8 => encoding_rs::ISO_8859_8,
            Self::Iso8859_8I => encoding_rs::ISO_8859_8_I,
            Self::Windows1255 => encoding_rs::WINDOWS_1255,
            Self::Iso8859_6 => encoding_rs::ISO_8859_6,
            Self::Windows1256 => encoding_rs::WINDOWS_1256,
            Self::Windows1258 => encoding_rs::WINDOWS_1258,
            Self::Windows874 => encoding_rs::WINDOWS_874,
            Self::ShiftJis => encoding_rs::SHIFT_JIS,
            Self::EucJp => encoding_rs::EUC_JP,
            Self::Iso2022Jp => encoding_rs::ISO_2022_JP,
            Self::Gbk => encoding_rs::GBK,
            Self::Gb18030 => encoding_rs::GB18030,
            Self::Big5 => encoding_rs::BIG5,
            Self::EucKr => encoding_rs::EUC_KR,
            Self::Utf16Be => encoding_rs::UTF_16BE,
            Self::Utf16Le => encoding_rs::UTF_16LE,
        }
    }

    /// Maps an `encoding_rs::Encoding` to our enum.
    fn from_encoding_rs(enc: &'static encoding_rs::Encoding) -> Option<Self> {
        Some(match enc {
            e if e == encoding_rs::UTF_8 => Self::Utf8,
            e if e == encoding_rs::WINDOWS_1252 => Self::Windows1252,
            e if e == encoding_rs::ISO_8859_15 => Self::Iso8859_15,
            e if e == encoding_rs::MACINTOSH => Self::Macintosh,
            e if e == encoding_rs::ISO_8859_2 => Self::Iso8859_2,
            e if e == encoding_rs::WINDOWS_1250 => Self::Windows1250,
            e if e == encoding_rs::ISO_8859_3 => Self::Iso8859_3,
            e if e == encoding_rs::WINDOWS_1254 => Self::Windows1254,
            e if e == encoding_rs::ISO_8859_4 => Self::Iso8859_4,
            e if e == encoding_rs::ISO_8859_10 => Self::Iso8859_10,
            e if e == encoding_rs::ISO_8859_13 => Self::Iso8859_13,
            e if e == encoding_rs::WINDOWS_1257 => Self::Windows1257,
            e if e == encoding_rs::ISO_8859_14 => Self::Iso8859_14,
            e if e == encoding_rs::ISO_8859_16 => Self::Iso8859_16,
            e if e == encoding_rs::ISO_8859_5 => Self::Iso8859_5,
            e if e == encoding_rs::WINDOWS_1251 => Self::Windows1251,
            e if e == encoding_rs::KOI8_R => Self::Koi8R,
            e if e == encoding_rs::KOI8_U => Self::Koi8U,
            e if e == encoding_rs::IBM866 => Self::Ibm866,
            e if e == encoding_rs::X_MAC_CYRILLIC => Self::XMacCyrillic,
            e if e == encoding_rs::ISO_8859_7 => Self::Iso8859_7,
            e if e == encoding_rs::WINDOWS_1253 => Self::Windows1253,
            e if e == encoding_rs::ISO_8859_8 => Self::Iso8859_8,
            e if e == encoding_rs::ISO_8859_8_I => Self::Iso8859_8I,
            e if e == encoding_rs::WINDOWS_1255 => Self::Windows1255,
            e if e == encoding_rs::ISO_8859_6 => Self::Iso8859_6,
            e if e == encoding_rs::WINDOWS_1256 => Self::Windows1256,
            e if e == encoding_rs::WINDOWS_1258 => Self::Windows1258,
            e if e == encoding_rs::WINDOWS_874 => Self::Windows874,
            e if e == encoding_rs::SHIFT_JIS => Self::ShiftJis,
            e if e == encoding_rs::EUC_JP => Self::EucJp,
            e if e == encoding_rs::ISO_2022_JP => Self::Iso2022Jp,
            e if e == encoding_rs::GBK => Self::Gbk,
            e if e == encoding_rs::GB18030 => Self::Gb18030,
            e if e == encoding_rs::BIG5 => Self::Big5,
            e if e == encoding_rs::EUC_KR => Self::EucKr,
            e if e == encoding_rs::UTF_16BE => Self::Utf16Be,
            e if e == encoding_rs::UTF_16LE => Self::Utf16Le,
            _ => return None,
        })
    }

    /// Decodes a byte slice from this encoding into a UTF-8 string.
    ///
    /// # Examples
    /// ```
    /// # use arena_terms::Encoding;
    /// let s = Encoding::Iso8859_1.decode(&[0x63, 0x61, 0x66, 0xE9]).unwrap();
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
            Self::Iso8859_1 => {
                let mut out = String::with_capacity(bytes.len());
                for &b in bytes {
                    out.push(b as char);
                }
                Ok(out)
            }
            _ => {
                let (cow, _, had_errors) = self.to_encoding_rs().decode(bytes);
                if had_errors {
                    return Err(TermError::Encoding(
                        format!("invalid {} sequence", self.name()).into(),
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
    /// let bytes = Encoding::Iso8859_1.encode("café").unwrap();
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
            Self::Iso8859_1 => {
                let mut out = Vec::with_capacity(s.len());
                for ch in s.chars() {
                    let cp = ch as u32;
                    if cp > 0xFF {
                        return Err(TermError::Encoding(
                            format!(
                                "character '{}' (U+{:04X}) not representable in iso-8859-1",
                                ch, cp
                            )
                            .into(),
                        ));
                    }
                    out.push(cp as u8);
                }
                Ok(out)
            }
            _ => {
                let (cow, _, had_errors) = self.to_encoding_rs().encode(s);
                if had_errors {
                    return Err(TermError::Encoding(
                        format!("string not representable in {}", self.name()).into(),
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
        assert_eq!(Encoding::from_name("ISO-8859-1"), Some(Encoding::Iso8859_1));
        assert_eq!(Encoding::from_name("latin1"), Some(Encoding::Iso8859_1));
        assert_eq!(Encoding::from_name("Windows-1252"), Some(Encoding::Windows1252));
        assert_eq!(Encoding::from_name("us-ascii"), Some(Encoding::Ascii));
        assert_eq!(Encoding::from_name("unknown"), None);
    }

    #[test]
    fn from_name_encoding_rs_labels() {
        assert_eq!(Encoding::from_name("shift_jis"), Some(Encoding::ShiftJis));
        assert_eq!(Encoding::from_name("euc-jp"), Some(Encoding::EucJp));
        assert_eq!(Encoding::from_name("gbk"), Some(Encoding::Gbk));
        assert_eq!(Encoding::from_name("big5"), Some(Encoding::Big5));
        assert_eq!(Encoding::from_name("koi8-r"), Some(Encoding::Koi8R));
        assert_eq!(Encoding::from_name("iso-8859-2"), Some(Encoding::Iso8859_2));
        assert_eq!(Encoding::from_name("windows-1251"), Some(Encoding::Windows1251));
        assert_eq!(Encoding::from_name("utf-16le"), Some(Encoding::Utf16Le));
        assert_eq!(Encoding::from_name("utf-16be"), Some(Encoding::Utf16Be));
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
            Encoding::Iso8859_1.decode(&[0x63, 0x61, 0x66, 0xE9]).unwrap(),
            "café"
        );
    }

    #[test]
    fn decode_latin1_full_range() {
        let bytes: Vec<u8> = (0u8..=255).collect();
        let s = Encoding::Iso8859_1.decode(&bytes).unwrap();
        assert_eq!(s.chars().count(), 256);
        assert_eq!(s.chars().last(), Some('\u{FF}'));
    }

    #[test]
    fn decode_windows1252() {
        assert_eq!(Encoding::Windows1252.decode(&[0x93]).unwrap(), "\u{201C}");
    }

    #[test]
    fn decode_windows1251_cyrillic() {
        // 0xCF 0xF0 0xE8 0xE2 0xE5 0xF2 = "Привет" in Windows-1251
        let bytes = &[0xCF, 0xF0, 0xE8, 0xE2, 0xE5, 0xF2];
        assert_eq!(Encoding::Windows1251.decode(bytes).unwrap(), "Привет");
    }

    #[test]
    fn decode_shift_jis() {
        // 0x82 0xB1 0x82 0xF1 = "こん" in Shift_JIS
        let bytes = &[0x82, 0xB1, 0x82, 0xF1];
        assert_eq!(Encoding::ShiftJis.decode(bytes).unwrap(), "こん");
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
            Encoding::Iso8859_1.encode("café").unwrap(),
            vec![0x63, 0x61, 0x66, 0xE9]
        );
    }

    #[test]
    fn encode_latin1_out_of_range() {
        assert!(Encoding::Iso8859_1.encode("Ā").is_err());
    }

    #[test]
    fn encode_windows1252() {
        assert_eq!(
            Encoding::Windows1252.encode("\u{201C}").unwrap(),
            vec![0x93]
        );
    }

    #[test]
    fn encode_windows1251_cyrillic() {
        assert_eq!(
            Encoding::Windows1251.encode("Привет").unwrap(),
            vec![0xCF, 0xF0, 0xE8, 0xE2, 0xE5, 0xF2]
        );
    }

    #[test]
    fn decode_encode_roundtrip() {
        for enc in [Encoding::Utf8, Encoding::Ascii, Encoding::Iso8859_1, Encoding::Windows1252] {
            let original = b"hello";
            let s = enc.decode(original).unwrap();
            let bytes = enc.encode(&s).unwrap();
            assert_eq!(&bytes, original, "roundtrip failed for {}", enc);
        }
    }

    #[test]
    fn encode_decode_roundtrip_latin1() {
        let original = "café";
        let bytes = Encoding::Iso8859_1.encode(original).unwrap();
        let s = Encoding::Iso8859_1.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    #[test]
    fn encode_decode_roundtrip_windows1251() {
        let original = "Привет";
        let bytes = Encoding::Windows1251.encode(original).unwrap();
        let s = Encoding::Windows1251.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    // -- Cyrillic encodings --

    #[test]
    fn decode_koi8r_cyrillic() {
        // "Привет" in KOI8-R
        let bytes = &[0xF0, 0xD2, 0xC9, 0xD7, 0xC5, 0xD4];
        assert_eq!(Encoding::Koi8R.decode(bytes).unwrap(), "Привет");
    }

    #[test]
    fn encode_koi8r_cyrillic() {
        let bytes = Encoding::Koi8R.encode("Привет").unwrap();
        assert_eq!(bytes, vec![0xF0, 0xD2, 0xC9, 0xD7, 0xC5, 0xD4]);
    }

    #[test]
    fn decode_koi8u_ukrainian() {
        // "Київ" in KOI8-U
        let bytes = &[0xEB, 0xC9, 0xA7, 0xD7];
        assert_eq!(Encoding::Koi8U.decode(bytes).unwrap(), "Київ");
    }

    #[test]
    fn decode_iso8859_5_cyrillic() {
        // "Мир" in ISO-8859-5: М=0xBC, и=0xD8, р=0xE0
        let bytes = &[0xBC, 0xD8, 0xE0];
        assert_eq!(Encoding::Iso8859_5.decode(bytes).unwrap(), "Мир");
    }

    #[test]
    fn encode_decode_roundtrip_koi8r() {
        let original = "Здравствуйте";
        let bytes = Encoding::Koi8R.encode(original).unwrap();
        let s = Encoding::Koi8R.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    // -- CJK encodings --

    #[test]
    fn decode_gbk_chinese() {
        // "你好" in GBK: 0xC4E3 0xBAC3
        let bytes = &[0xC4, 0xE3, 0xBA, 0xC3];
        assert_eq!(Encoding::Gbk.decode(bytes).unwrap(), "你好");
    }

    #[test]
    fn encode_gbk_chinese() {
        let bytes = Encoding::Gbk.encode("你好").unwrap();
        assert_eq!(bytes, vec![0xC4, 0xE3, 0xBA, 0xC3]);
    }

    #[test]
    fn decode_big5_traditional_chinese() {
        // "世界" in Big5: 0xA5 0x40 0xAC 0xC9
        let bytes = &[0xA5, 0x40, 0xAC, 0xC9];
        assert_eq!(Encoding::Big5.decode(bytes).unwrap(), "世界");
    }

    #[test]
    fn decode_euc_kr_korean() {
        // "한글" in EUC-KR: 0xC7 0xD1 0xB1 0xDB
        let bytes = &[0xC7, 0xD1, 0xB1, 0xDB];
        assert_eq!(Encoding::EucKr.decode(bytes).unwrap(), "한글");
    }

    #[test]
    fn decode_euc_jp_japanese() {
        // "日本" in EUC-JP: 0xC6 0xFC 0xCB 0xDC
        let bytes = &[0xC6, 0xFC, 0xCB, 0xDC];
        assert_eq!(Encoding::EucJp.decode(bytes).unwrap(), "日本");
    }

    #[test]
    fn encode_decode_roundtrip_shift_jis() {
        let original = "東京タワー";
        let bytes = Encoding::ShiftJis.encode(original).unwrap();
        let s = Encoding::ShiftJis.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    #[test]
    fn encode_decode_roundtrip_gb18030() {
        let original = "中文测试";
        let bytes = Encoding::Gb18030.encode(original).unwrap();
        let s = Encoding::Gb18030.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    #[test]
    fn encode_decode_roundtrip_euc_kr() {
        let original = "서울";
        let bytes = Encoding::EucKr.encode(original).unwrap();
        let s = Encoding::EucKr.decode(&bytes).unwrap();
        assert_eq!(s, original);
    }

    #[test]
    fn name_roundtrip() {
        for enc in [
            Encoding::Utf8, Encoding::Ascii, Encoding::Iso8859_1, Encoding::Windows1252,
            Encoding::Windows1251, Encoding::Koi8R, Encoding::ShiftJis, Encoding::EucJp,
            Encoding::Gbk, Encoding::Big5, Encoding::EucKr, Encoding::Utf16Be,
        ] {
            assert_eq!(
                Encoding::from_name(enc.name()),
                Some(enc),
                "name roundtrip failed for {:?} (name={})",
                enc,
                enc.name()
            );
        }
    }
}
