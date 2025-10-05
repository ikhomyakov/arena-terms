use std::collections::HashMap;
use std::slice::Iter;

/// A simple symbol table mapping strings to numeric indices.
///
/// `Symtab` maintains a bidirectional mapping between symbol names and their
/// integer IDs, preserving insertion order. It is commonly used by the lexer
/// and parser generators to keep track of terminals, nonterminals, and token
/// identifiers.
///
/// Internally, it stores:
/// - a `HashMap` for fast name-to-index lookup,
/// - and a `Vec` for ordered index-to-name retrieval.
#[derive(Default, Debug)]
pub struct Symtab {
    /// Maps symbol names to their numeric indices.
    map: HashMap<String, usize>,

    /// Stores symbol names in insertion order for index-based lookup.
    vec: Vec<String>,
}

/// Implementation of [`Symtab`] methods.
///
/// Provides constructors, lookup, insertion, and debugging utilities
/// for symbol management.
impl Symtab {
    /// Creates a new, empty symbol table.
    ///
    /// # Returns
    /// A fresh [`Symtab`] with no entries.
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            vec: Vec::new(),
        }
    }

    /// Adds a symbol to the table, returning its index.
    ///
    /// If the symbol already exists, its existing index is returned.
    ///
    /// # Parameters
    /// - `sym`: The symbol name to insert.
    ///
    /// # Returns
    /// The numeric index of the symbol.
    pub fn add(&mut self, sym: &str) -> usize {
        if let Some(&idx) = self.map.get(sym) {
            return idx;
        }
        let idx = self.vec.len();
        let owned = sym.to_owned();
        self.vec.push(owned.clone());
        self.map.insert(owned, idx);
        idx
    }

    /// Returns an iterator over all stored symbols in insertion order.
    ///
    /// # Returns
    /// An iterator yielding `&String` references to each symbol.
    pub fn iter(&self) -> Iter<'_, String> {
        self.vec.iter()
    }

    /// Returns all symbols as a vector of strings.
    ///
    /// This produces a cloned list of all stored names.
    pub fn vec(&self) -> Vec<String> {
        self.vec.clone()
    }

    /// Extends the table with all symbols from another [`Symtab`].
    ///
    /// This method appends all symbols from `tab` to this table’s internal vector.
    /// It does **not** perform deduplication, and indices will not be merged.
    ///
    /// # Parameters
    /// - `tab`: Another symbol table whose contents will be appended.
    pub fn extend(&mut self, tab: &Symtab) {
        self.vec.extend_from_slice(&tab.vec);
    }

    /// Looks up the index of a symbol by name.
    ///
    /// # Parameters
    /// - `sym`: The symbol name to search for.
    ///
    /// # Returns
    /// `Some(index)` if found, or `None` if the symbol is not in the table.
    pub fn _idx(&self, sym: &str) -> Option<usize> {
        self.map.get(sym).copied()
    }

    /// Returns the symbol string associated with a given index.
    ///
    /// # Parameters
    /// - `idx`: The symbol index to look up.
    ///
    /// # Returns
    /// `Some(&str)` if the index is valid, or `None` otherwise.
    pub fn sym(&self, idx: usize) -> Option<&str> {
        self.vec.get(idx).map(|x| x.as_str())
    }

    /// Returns the number of symbols stored in the table.
    ///
    /// # Returns
    /// The total number of entries.
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Prints the contents of the symbol table to standard output.
    ///
    /// Useful for debugging or inspecting symbol indices.
    pub fn _print(&self) {
        for (i, s) in self.vec.iter().enumerate() {
            println!("{}: {}", i, s);
        }
    }
}

/// Unit tests for the [`Symtab`] implementation.
#[cfg(test)]
mod tests {
    use super::Symtab;

    #[test]
    fn test_new_is_empty() {
        let st = Symtab::new();
        assert_eq!(st._idx("anything"), None);
        assert_eq!(st.sym(0), None);
    }

    #[test]
    fn test_add_and_retrieve() {
        let mut st = Symtab::new();
        let i_foo = st.add("foo");
        assert_eq!(i_foo, 0);
        assert_eq!(st._idx("foo"), Some(0));
        assert_eq!(st.sym(0), Some("foo"));

        let i_bar = st.add("bar");
        assert_eq!(i_bar, 1);
        assert_eq!(st._idx("bar"), Some(1));
        assert_eq!(st.sym(1), Some("bar"));
    }

    #[test]
    fn test_duplicate_add_returns_same_index() {
        let mut st = Symtab::new();
        let first = st.add("dup");
        let second = st.add("dup");
        assert_eq!(first, second);
        assert_eq!(st._idx("dup"), Some(first));
        assert_eq!(st.sym(first), Some("dup"));
        // only one unique entry
        assert_eq!(st.sym(1), None); // nothing else was inserted
    }

    #[test]
    fn test_nonexistent_lookup() {
        let mut st = Symtab::new();
        st.add("existing");
        assert_eq!(st._idx("missing"), None);
        assert_eq!(st.sym(42), None);
    }

    #[test]
    fn test_many_symbols_and_consistency() {
        let mut st = Symtab::new();
        let names = ["a", "b", "c", "a", "d", "b"];
        let mut seen = std::collections::HashSet::new();
        for &name in &names {
            let idx = st.add(name);
            assert_eq!(st.sym(idx), Some(name));
            seen.insert(name);
        }
        // number of unique symbols should equal size of seen
        assert_eq!(st.vec.len(), seen.len());
        // all stored symbols are retrievable via idx
        for name in seen {
            let idx = st._idx(name).expect("should have index");
            assert_eq!(st.sym(idx), Some(name));
        }
    }
}
