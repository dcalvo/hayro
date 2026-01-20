//! Ported from <https://github.com/mozilla/pdf.js/blob/master/src/core/cmap.js>

use std::collections::HashMap;

const MAX_MAP_RANGE: u32 = (1 << 24) - 1; // 0xFFFFFF

#[derive(Debug, Clone)]
pub(crate) struct CMap {
    codespace_ranges: [Vec<u32>; 4],
    /// Maps char codes to Unicode strings (supports multi-char mappings like ligatures).
    map: HashMap<u32, String>,
    name: String,
    vertical: bool,
}

impl CMap {
    pub(crate) fn new() -> Self {
        Self {
            codespace_ranges: [Vec::new(), Vec::new(), Vec::new(), Vec::new()],
            map: HashMap::new(),
            name: String::new(),
            vertical: false,
        }
    }

    pub(crate) fn identity_h() -> Self {
        let mut cmap = Self::new();

        cmap.name = "Identity-H".to_string();
        cmap.vertical = false;
        cmap.add_codespace_range(2, 0, 0xFFFF);
        cmap
    }

    pub(crate) fn identity_v() -> Self {
        let mut cmap = Self::new();

        cmap.name = "Identity-V".to_string();
        cmap.vertical = true;
        cmap.add_codespace_range(2, 0, 0xFFFF);
        cmap
    }

    pub(crate) fn is_vertical(&self) -> bool {
        self.vertical
    }

    pub(crate) fn is_identity_cmap(&self) -> bool {
        (self.name == "Identity-H" || self.name == "Identity-V") && self.map.is_empty()
    }

    /// Looks up the Unicode text for a character code.
    ///
    /// Returns a string which may contain multiple characters (e.g., for ligatures).
    /// Use this for ToUnicode CMaps.
    pub(crate) fn lookup_code(&self, code: u32) -> Option<String> {
        if let Some(value) = self.map.get(&code) {
            Some(value.clone())
        } else if self.is_identity_cmap() {
            if code <= 0xFFFF {
                char::from_u32(code).map(|c| c.to_string())
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Looks up the CID (character identifier) for a character code.
    ///
    /// Returns a u32 CID value. Use this for encoding CMaps that map
    /// character codes to CIDs (glyph indices), not for ToUnicode lookups.
    pub(crate) fn lookup_cid(&self, code: u32) -> Option<u32> {
        if let Some(value) = self.map.get(&code) {
            // For CID mappings, we expect single characters representing the CID
            value.chars().next().map(|c| c as u32)
        } else if self.is_identity_cmap() {
            if code <= 0xFFFF { Some(code) } else { None }
        } else {
            None
        }
    }

    fn add_codespace_range(&mut self, n: usize, low: u32, high: u32) {
        if n > 0 && n <= 4 {
            self.codespace_ranges[n - 1].push(low);
            self.codespace_ranges[n - 1].push(high);
        }
    }

    fn map_cid_range(&mut self, low: u32, high: u32, dst_low: u32) -> Option<()> {
        if high.checked_sub(low)? > MAX_MAP_RANGE {
            return None;
        }

        let mut current_low = low;
        let mut current_dst = dst_low;
        while current_low <= high {
            if let Some(c) = char::from_u32(current_dst) {
                self.map.insert(current_low, c.to_string());
            }
            current_low += 1;
            current_dst += 1;
        }

        Some(())
    }

    fn map_bf_range(&mut self, low: u32, high: u32, dst_low: u32) -> Option<()> {
        if high.checked_sub(low)? > MAX_MAP_RANGE {
            return None;
        }

        let mut current_low = low;
        let mut current_dst = dst_low;

        while current_low <= high {
            if let Some(c) = char::from_u32(current_dst) {
                self.map.insert(current_low, c.to_string());
            }
            current_dst += 1;
            current_low += 1;
        }

        Some(())
    }

    fn map_bf_range_to_array(&mut self, low: u32, high: u32, array: Vec<String>) -> Option<()> {
        if high.checked_sub(low)? > MAX_MAP_RANGE {
            return None;
        }

        let mut current_low = low;
        let mut i = 0;

        while current_low <= high && i < array.len() {
            self.map.insert(current_low, array[i].clone());
            current_low += 1;
            i += 1;
        }

        Some(())
    }

    fn map_one(&mut self, src: u32, dst: String) {
        self.map.insert(src, dst);
    }

    pub(crate) fn read_code(&self, bytes: &[u8], offset: usize) -> (u32, usize) {
        let mut c = 0_u32;

        for n in 0..4.min(bytes.len() - offset) {
            if offset + n >= bytes.len() {
                break;
            }

            c = (c << 8) | bytes[offset + n] as u32;

            let codespace_range = &self.codespace_ranges[n];
            for chunk in codespace_range.chunks(2) {
                if chunk.len() == 2 {
                    let low = chunk[0];
                    let high = chunk[1];
                    if c >= low && c <= high {
                        return (c, n + 1);
                    }
                }
            }
        }

        (0, 1)
    }
}

/// Decode a hex string as UTF-16BE to produce a Unicode string.
///
/// ToUnicode CMap hex strings like `<00740069>` represent UTF-16BE code units.
/// This decodes them properly: `<00740069>` → "ti" (two chars: U+0074 't', U+0069 'i').
///
/// For odd-length byte sequences, we prepend a zero byte to form complete
/// UTF-16BE code units: `<01>` → `<0001>` → U+0001.
fn decode_utf16be(bytes: &[u8]) -> String {
    // If odd number of bytes, prepend a zero byte
    let bytes = if bytes.len() % 2 == 1 {
        let mut padded = vec![0u8];
        padded.extend_from_slice(bytes);
        padded
    } else {
        bytes.to_vec()
    };

    // Convert bytes to u16 code units (big-endian)
    let code_units: Vec<u16> = bytes
        .chunks(2)
        .map(|chunk| u16::from_be_bytes([chunk[0], chunk[1]]))
        .collect();

    // Decode UTF-16 to String (handles surrogate pairs)
    char::decode_utf16(code_units)
        .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

fn str_to_int(s: &str) -> u32 {
    let mut a = 0_u32;
    for ch in s.chars() {
        // Since we created these strings from bytes using char::from(byte),
        // we can safely cast back to get the original byte value
        a = (a << 8) | (ch as u32 & 0xFF);
    }
    a
}

/// For source codes (like `<019F>`), we want raw bytes as an integer.
fn hex_bytes_to_int(bytes: &[u8]) -> u32 {
    let mut a = 0_u32;
    for &byte in bytes {
        a = (a << 8) | (byte as u32);
    }
    a
}

fn expect_string(obj: &Token) -> Option<String> {
    match obj {
        Token::HexString(bytes) => {
            // Convert bytes to string the same way pdf.js does: using String.fromCharCode
            // Each byte becomes a character with that character code
            let mut result = String::new();
            for &byte in bytes {
                result.push(char::from(byte));
            }
            Some(result)
        }
        Token::String(s) => Some(s.clone()),
        _ => None,
    }
}

/// Get the raw bytes from a hex string token.
fn expect_hex_bytes(obj: &Token) -> Option<&[u8]> {
    match obj {
        Token::HexString(bytes) => Some(bytes),
        _ => None,
    }
}

fn expect_int(obj: &Token) -> Option<i32> {
    match obj {
        Token::Integer(i) => Some(*i),
        _ => None,
    }
}

#[derive(Debug, Clone)]
enum Token {
    String(String),
    HexString(Vec<u8>), // Raw bytes from hex string
    Integer(i32),
    Command(String),
    Name(String),
    Eof,
}

struct CMapLexer<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> CMapLexer<'a> {
    fn new(input: &'a str) -> Self {
        CMapLexer { input, position: 0 }
    }

    fn get_obj(&mut self) -> Token {
        self.skip_whitespace();

        if self.position >= self.input.len() {
            return Token::Eof;
        }

        let remaining = &self.input[self.position..];

        // Handle PostScript comments (% to end of line)
        if remaining.starts_with('%') {
            // Skip to end of line
            while self.position < self.input.len() {
                let ch = self.input.as_bytes()[self.position] as char;
                self.position += 1;
                if ch == '\n' || ch == '\r' {
                    break;
                }
            }
            // Skip any additional whitespace and try again
            self.skip_whitespace();
            return self.get_obj();
        }

        // Handle dictionary delimiters
        if remaining.starts_with(">>") {
            self.position += 2;
            return Token::Command(">>".to_string());
        }

        // Handle hex strings and dictionary start
        if remaining.starts_with('<') {
            return self.parse_hex_string();
        }

        // Handle PostScript strings (parentheses)
        if remaining.starts_with('(') {
            return self.parse_ps_string();
        }

        // Handle arrays
        if remaining.starts_with('[') {
            return self.parse_array();
        }

        if remaining.starts_with(']') {
            self.position += 1;
            return Token::Command("]".to_string());
        }

        // Handle names
        if remaining.starts_with('/') {
            return self.parse_name();
        }

        // Handle numbers and commands
        self.parse_token()
    }

    fn skip_whitespace(&mut self) {
        while self.position < self.input.len() {
            let ch = self.input.as_bytes()[self.position] as char;
            if ch.is_whitespace() {
                self.position += 1;
            } else {
                break;
            }
        }
    }

    fn parse_hex_string(&mut self) -> Token {
        // Check if it's actually a dictionary delimiter <<
        let remaining = &self.input[self.position..];
        if remaining.starts_with("<<") {
            self.position += 2;
            return Token::Command("<<".to_string());
        }

        self.position += 1; // Skip '<'
        let mut hex_string = String::new();

        while self.position < self.input.len() {
            let ch = self.input.as_bytes()[self.position] as char;
            if ch == '>' {
                self.position += 1;
                break;
            }
            if ch.is_ascii_hexdigit() {
                hex_string.push(ch);
            }
            self.position += 1;
        }

        // Convert hex string to raw bytes
        let mut result_bytes = Vec::new();
        for chunk in hex_string.chars().collect::<Vec<_>>().chunks(2) {
            let hex_byte = if chunk.len() == 2 {
                format!("{}{}", chunk[0], chunk[1])
            } else {
                format!("{}0", chunk[0])
            };

            if let Ok(byte_val) = u8::from_str_radix(&hex_byte, 16) {
                result_bytes.push(byte_val);
            }
        }

        Token::HexString(result_bytes)
    }

    fn parse_ps_string(&mut self) -> Token {
        self.position += 1; // Skip '('
        let mut string = String::new();
        let mut paren_depth = 1;

        while self.position < self.input.len() && paren_depth > 0 {
            let ch = self.input.as_bytes()[self.position] as char;
            match ch {
                '(' => {
                    paren_depth += 1;
                    string.push(ch);
                }
                ')' => {
                    paren_depth -= 1;
                    if paren_depth > 0 {
                        string.push(ch);
                    }
                }
                '\\' => {
                    // Handle escape sequences
                    self.position += 1;
                    if self.position < self.input.len() {
                        let escaped = self.input.as_bytes()[self.position] as char;
                        string.push('\\');
                        string.push(escaped);
                    }
                }
                _ => string.push(ch),
            }
            self.position += 1;
        }

        Token::String(string)
    }

    fn parse_array(&mut self) -> Token {
        self.position += 1; // Skip '['
        Token::Command("[".to_string())
    }

    fn parse_name(&mut self) -> Token {
        self.position += 1; // Skip '/'
        let mut name = String::new();

        while self.position < self.input.len() {
            let ch = self.input.as_bytes()[self.position] as char;
            if ch.is_whitespace() || "[]<>(){}/%".contains(ch) {
                break;
            }
            name.push(ch);
            self.position += 1;
        }

        Token::Name(name)
    }

    fn parse_token(&mut self) -> Token {
        let mut token = String::new();

        while self.position < self.input.len() {
            let ch = self.input.as_bytes()[self.position] as char;
            if ch.is_whitespace() || "[]<>(){}/%".contains(ch) {
                break;
            }
            token.push(ch);
            self.position += 1;
        }

        if token.is_empty() {
            return Token::Eof;
        }

        if let Ok(num) = token.parse::<i32>() {
            Token::Integer(num)
        } else {
            Token::Command(token)
        }
    }
}

fn parse_bf_char(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    loop {
        let obj = lexer.get_obj();
        match obj {
            Token::Eof => break,
            Token::Command(cmd) if cmd == "endbfchar" => return Some(()),
            ref token => {
                // Source is a raw byte sequence interpreted as an integer
                let src = if let Some(bytes) = expect_hex_bytes(token) {
                    hex_bytes_to_int(bytes)
                } else {
                    let src_str = expect_string(token)?;
                    str_to_int(&src_str)
                };

                let dst_obj = lexer.get_obj();
                // Destination is UTF-16BE encoded Unicode
                let dst_text = if let Some(bytes) = expect_hex_bytes(&dst_obj) {
                    decode_utf16be(bytes)
                } else {
                    expect_string(&dst_obj)?
                };

                if !dst_text.is_empty() {
                    cmap.map_one(src, dst_text);
                }
            }
        }
    }

    Some(())
}

fn parse_bf_range(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    loop {
        let obj = lexer.get_obj();
        match obj {
            Token::Eof => break,
            Token::Command(cmd) if cmd == "endbfrange" => return Some(()),
            ref token => {
                // Source range bounds are raw byte sequences as integers
                let low = if let Some(bytes) = expect_hex_bytes(token) {
                    hex_bytes_to_int(bytes)
                } else {
                    let low_str = expect_string(token)?;
                    str_to_int(&low_str)
                };

                let high_obj = lexer.get_obj();
                let high = if let Some(bytes) = expect_hex_bytes(&high_obj) {
                    hex_bytes_to_int(bytes)
                } else {
                    let high_str = expect_string(&high_obj)?;
                    str_to_int(&high_str)
                };

                let dst_obj = lexer.get_obj();
                match dst_obj {
                    Token::Integer(dst_low) => {
                        cmap.map_bf_range(low, high, dst_low as u32)?;
                    }
                    ref token => {
                        if let Some(bytes) = expect_hex_bytes(token) {
                            // Destination is UTF-16BE - decode to get starting code point
                            let text = decode_utf16be(bytes);
                            if let Some(first_char) = text.chars().next() {
                                cmap.map_bf_range(low, high, first_char as u32)?;
                            }
                        } else if let Token::Command(cmd) = token {
                            if cmd == "[" {
                                let mut array: Vec<String> = Vec::new();
                                loop {
                                    let array_obj = lexer.get_obj();
                                    match array_obj {
                                        Token::Command(cmd) if cmd == "]" => break,
                                        Token::Eof => break,
                                        Token::Integer(val) => {
                                            if let Some(c) = char::from_u32(val as u32) {
                                                array.push(c.to_string());
                                            }
                                        }
                                        ref arr_token => {
                                            if let Some(bytes) = expect_hex_bytes(arr_token) {
                                                // UTF-16BE decode each array element
                                                let text = decode_utf16be(bytes);
                                                if !text.is_empty() {
                                                    array.push(text);
                                                }
                                            }
                                        }
                                    }
                                }
                                cmap.map_bf_range_to_array(low, high, array)?;
                            } else {
                                return None;
                            }
                        } else {
                            return None;
                        }
                    }
                }
            }
        }
    }

    Some(())
}

fn parse_cid_char(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    loop {
        let obj = lexer.get_obj();
        match obj {
            Token::Eof => break,
            Token::Command(cmd) if cmd == "endcidchar" => return Some(()),
            ref token => {
                let src = if let Some(bytes) = expect_hex_bytes(token) {
                    hex_bytes_to_int(bytes)
                } else {
                    let src_str = expect_string(token)?;
                    str_to_int(&src_str)
                };
                let dst_obj = lexer.get_obj();
                let dst = expect_int(&dst_obj)?;
                if let Some(c) = char::from_u32(dst as u32) {
                    cmap.map_one(src, c.to_string());
                }
            }
        }
    }

    Some(())
}

fn parse_cid_range(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    loop {
        let obj = lexer.get_obj();
        match obj {
            Token::Eof => break,
            Token::Command(cmd) if cmd == "endcidrange" => return Some(()),
            ref token => {
                let low = if let Some(bytes) = expect_hex_bytes(token) {
                    hex_bytes_to_int(bytes)
                } else {
                    let low_str = expect_string(token)?;
                    str_to_int(&low_str)
                };

                let high_obj = lexer.get_obj();
                let high = if let Some(bytes) = expect_hex_bytes(&high_obj) {
                    hex_bytes_to_int(bytes)
                } else {
                    let high_str = expect_string(&high_obj)?;
                    str_to_int(&high_str)
                };

                let dst_obj = lexer.get_obj();
                let dst_low = expect_int(&dst_obj)?;

                cmap.map_cid_range(low, high, dst_low as u32)?;
            }
        }
    }

    Some(())
}

fn parse_codespace_range(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    loop {
        let obj = lexer.get_obj();
        match obj {
            Token::Eof => break,
            Token::Command(cmd) if cmd == "endcodespacerange" => return Some(()),
            ref token => {
                let (low, n) = if let Some(bytes) = expect_hex_bytes(token) {
                    (hex_bytes_to_int(bytes), bytes.len())
                } else {
                    let low_str = expect_string(token)?;
                    if low_str.is_empty() {
                        continue;
                    }
                    (str_to_int(&low_str), low_str.chars().count())
                };

                let high_obj = lexer.get_obj();
                let (high, high_n) = if let Some(bytes) = expect_hex_bytes(&high_obj) {
                    (hex_bytes_to_int(bytes), bytes.len())
                } else {
                    let high_str = expect_string(&high_obj)?;
                    if high_str.is_empty() {
                        return None;
                    }
                    (str_to_int(&high_str), high_str.chars().count())
                };

                // Use the larger of the two sizes for the codespace range
                cmap.add_codespace_range(n.max(high_n), low, high);
            }
        }
    }

    Some(())
}

fn parse_wmode(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    let obj = lexer.get_obj();
    if let Some(val) = expect_int(&obj) {
        cmap.vertical = val != 0;
    }

    Some(())
}

fn parse_cmap_name(cmap: &mut CMap, lexer: &mut CMapLexer<'_>) -> Option<()> {
    let obj = lexer.get_obj();
    match obj {
        Token::Name(name) => {
            cmap.name = name;
            Some(())
        }
        _ => Some(()), // Don't error on unexpected tokens, just ignore
    }
}

pub(super) fn parse_cmap(input: &str) -> Option<CMap> {
    if !input.is_ascii() {
        return None;
    }

    let mut cmap = CMap::new();
    let mut lexer = CMapLexer::new(input);

    loop {
        let obj = lexer.get_obj();
        match obj {
            Token::Eof => break,
            Token::Name(ref name) => {
                if name == "WMode" {
                    parse_wmode(&mut cmap, &mut lexer)?;
                } else if name == "CMapName" {
                    parse_cmap_name(&mut cmap, &mut lexer)?;
                }
            }
            Token::Command(ref cmd) => {
                match cmd.as_str() {
                    "endcmap" => break,
                    "usecmap" => {
                        // TODO: Implement
                    }
                    "begincodespacerange" => {
                        parse_codespace_range(&mut cmap, &mut lexer)?;
                    }
                    "beginbfchar" => {
                        parse_bf_char(&mut cmap, &mut lexer)?;
                    }
                    "begincidchar" => {
                        parse_cid_char(&mut cmap, &mut lexer)?;
                    }
                    "beginbfrange" => {
                        parse_bf_range(&mut cmap, &mut lexer)?;
                    }
                    "begincidrange" => {
                        parse_cid_range(&mut cmap, &mut lexer)?;
                    }
                    "def" | "dict" | "begin" | "end" | "findresource" | "<<" | ">>" | "pop"
                    | "currentdict" | "defineresource" => {}
                    _ => {
                        // Skip any other unknown commands.
                    }
                }
            }
            Token::String(_) | Token::HexString(_) | Token::Integer(_) => {
                // Skip standalone tokens that aren't part of a command we recognize.
            }
        }
    }

    Some(cmap)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_beginbfchar() {
        let input = r#"2 beginbfchar
<03> <00>
<04> <01>
endbfchar"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert_eq!(cmap.lookup_code(0x03), Some("\0".to_string()));
        assert_eq!(cmap.lookup_code(0x04), Some("\u{01}".to_string()));
        assert!(cmap.lookup_code(0x05).is_none());
    }

    #[test]
    fn test_parse_beginbfrange_with_range() {
        let input = r#"1 beginbfrange
<06> <0B> 0
endbfrange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert!(cmap.lookup_code(0x05).is_none());
        assert_eq!(cmap.lookup_code(0x06), Some("\0".to_string()));
        assert_eq!(cmap.lookup_code(0x0b), Some("\u{05}".to_string()));
        assert!(cmap.lookup_code(0x0c).is_none());
    }

    #[test]
    fn test_parse_beginbfrange_with_array() {
        let input = r#"1 beginbfrange
<0D> <12> [ 0 1 2 3 4 5 ]
endbfrange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert!(cmap.lookup_code(0x0c).is_none());
        assert_eq!(cmap.lookup_code(0x0d), Some("\0".to_string()));
        assert_eq!(cmap.lookup_code(0x12), Some("\u{05}".to_string()));
        assert!(cmap.lookup_code(0x13).is_none());
    }

    #[test]
    fn test_parse_beginbfrange_with_hex_array() {
        // Test case from real PDF: em-dash (U+2014) mapped via array
        let input = r#"1 beginbfrange
<00B2> <00B2> [<2014>]
endbfrange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert!(cmap.lookup_code(0xB1).is_none());
        assert_eq!(cmap.lookup_code(0xB2), Some("\u{2014}".to_string())); // em-dash
        assert!(cmap.lookup_code(0xB3).is_none());
    }

    #[test]
    fn test_parse_beginbfrange_with_high_byte_hex_array() {
        // Test hex strings with bytes >= 0x80
        let input = r#"1 beginbfrange
<00B3> <00B3> [<00E9>]
endbfrange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert_eq!(cmap.lookup_code(0xB3), Some("é".to_string())); // é (U+00E9)
    }

    #[test]
    fn test_parse_begincidchar() {
        let input = r#"1 begincidchar
<14> 0
endcidchar"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert_eq!(cmap.lookup_code(0x14), Some("\0".to_string()));
        assert!(cmap.lookup_code(0x15).is_none());
    }

    #[test]
    fn test_parse_begincidrange() {
        let input = r#"1 begincidrange
<0016> <001B> 0
endcidrange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert!(cmap.lookup_code(0x15).is_none());
        assert_eq!(cmap.lookup_code(0x16), Some("\0".to_string()));
        assert_eq!(cmap.lookup_code(0x1b), Some("\u{05}".to_string()));
        assert!(cmap.lookup_code(0x1c).is_none());
    }

    #[test]
    fn test_parse_4_byte_codespace_ranges() {
        let input = r#"1 begincodespacerange
<8EA1A1A1> <8EA1FEFE>
endcodespacerange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        let test_bytes = [0x8E, 0xA1, 0xA1, 0xA1];
        let (charcode, length) = cmap.read_code(&test_bytes, 0);
        assert_eq!(charcode, 0x8ea1a1a1);
        assert_eq!(length, 4);
    }

    #[test]
    fn test_parse_cmap_name() {
        let input = r#"/CMapName /Identity-H def"#.to_string();

        let cmap = parse_cmap(&input).unwrap();
        assert_eq!(cmap.name, "Identity-H");
    }

    #[test]
    fn test_parse_wmode() {
        let input = r#"/WMode 1 def"#.to_string();

        let cmap = parse_cmap(&input).unwrap();
        assert!(cmap.vertical);
    }

    #[test]
    fn test_identity_h_cmap() {
        let cmap = CMap::identity_h();

        assert_eq!(cmap.name, "Identity-H");
        assert!(!cmap.vertical);

        assert_eq!(cmap.lookup_code(0x41), Some("A".to_string())); // U+0041 = 'A'
        assert_eq!(cmap.lookup_code(0x1234), Some("\u{1234}".to_string()));
        assert_eq!(cmap.lookup_code(0xFFFF), Some("\u{FFFF}".to_string()));
        assert_eq!(cmap.lookup_code(0x10000), None);

        let test_bytes = [0x12, 0x34];
        let (charcode, length) = cmap.read_code(&test_bytes, 0);
        assert_eq!(charcode, 0x1234);
        assert_eq!(length, 2);
    }

    #[test]
    fn test_identity_v_cmap() {
        let cmap = CMap::identity_v();

        assert_eq!(cmap.name, "Identity-V");
        assert!(cmap.vertical);

        assert_eq!(cmap.lookup_code(0x41), Some("A".to_string())); // U+0041 = 'A'
        assert_eq!(cmap.lookup_code(0x1234), Some("\u{1234}".to_string()));
        assert_eq!(cmap.lookup_code(0xFFFF), Some("\u{FFFF}".to_string()));
        assert_eq!(cmap.lookup_code(0x10000), None);
    }

    #[test]
    fn test_simple_cidrange() {
        let input = r#"1 begincidrange
<00> <FF> 0
endcidrange"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        // Should map codes 0x00-0xFF to CIDs 0-255
        assert_eq!(cmap.lookup_code(0x00), Some("\0".to_string()));
        assert_eq!(cmap.lookup_code(0x41), Some("A".to_string())); // 65 = 'A'
        assert_eq!(cmap.lookup_code(0xFF), Some("\u{FF}".to_string())); // 255
        assert_eq!(cmap.lookup_code(0x100), None);
    }

    #[test]
    fn test_complex_cmap_with_postscript() {
        let input = r#"/CIDInit /ProcSet findresource begin
12 dict begin
begincmap
/CIDSystemInfo
<< /Registry (Adobe)
/Ordering (Identity)
/Supplement 0
>> def
/CMapName /Identity-H def
/CMapType 2 def
1 begincodespacerange
<00> <FF>
endcodespacerange
1 begincidrange
<00> <FF> 0
endcidrange
endcmap
CMapName currentdict /CMap defineresource pop
end
end"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();

        assert_eq!(cmap.lookup_code(0x00), Some("\0".to_string()));
        assert_eq!(cmap.lookup_code(0x41), Some("A".to_string())); // 65 = 'A'
        assert_eq!(cmap.lookup_code(0xFF), Some("\u{FF}".to_string())); // 255
        assert_eq!(cmap.lookup_code(0x100), None);
        assert_eq!(cmap.name, "Identity-H");
    }

    #[test]
    fn test_parse_beginbfchar_ligature() {
        // "ti" ligature: <019F> maps to U+0074 U+0069 ("ti")
        // This is the key test for multi-character UTF-16BE mappings
        let input = r#"1 beginbfchar
<019F> <00740069>
endbfchar"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();
        assert_eq!(cmap.lookup_code(0x019F), Some("ti".to_string()));
    }

    #[test]
    fn test_parse_beginbfchar_ffi_ligature() {
        // "ffi" ligature: multiple code points
        let input = r#"1 beginbfchar
<01A0> <006600660069>
endbfchar"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();
        assert_eq!(cmap.lookup_code(0x01A0), Some("ffi".to_string()));
    }

    #[test]
    fn test_utf16be_surrogate_pairs() {
        // Test emoji that requires surrogate pairs: 😀 U+1F600
        // UTF-16BE: D83D DE00
        let input = r#"1 beginbfchar
<01> <D83DDE00>
endbfchar"#
            .to_string();

        let cmap = parse_cmap(&input).unwrap();
        assert_eq!(cmap.lookup_code(0x01), Some("😀".to_string()));
    }
}
