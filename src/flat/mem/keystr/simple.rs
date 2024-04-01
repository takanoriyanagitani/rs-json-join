//! Joins a larger row set and a smaller row set using string keys.
//!
//! - [`Merge`], [`Joined`] -> [`Map<String, Value>`]
//! - [`LargerToKey`], [`LargerRow`], [`SmallerRows`] -> [`Joined`]
//!   - [`ValueToWriter`], key string -> [`LargerToKey`]
//!   - [`SmallerToKey`], [`SmallerRow`] iterator -> [`SmallerRows`]
//!     - [`ValueToString`], key string -> [`SmallerToKey`]

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use serde_json::{Map, Value};

/// Creates a merged [`Map`] from a [`Joined`] using a [`Merge`].
pub struct MergeJoined<L, S, M> {
    /// Creates a [`Joined`].
    pub larger2key: L,

    /// Creates a [`SmallerRows`].
    pub smaller2key: S,

    /// Creates a [`Map`] from a [`LargerRow`] and a [`SmallerRow`].
    pub merger: M,
}

impl<L, S, M> MergeJoined<L, S, M>
where
    S: SmallerToKey,
{
    pub fn lines2smaller<I>(&self, lines: I) -> SmallerRows
    where
        I: Iterator<Item = String>,
    {
        let smaller =
            lines.flat_map(|line: String| serde_json::from_str::<SmallerRow>(line.as_str()).ok());
        self.smaller2key.rows2map(smaller)
    }

    #[cfg(feature = "std")]
    pub fn read2smaller<R>(&self, rdr: R) -> SmallerRows
    where
        R: std::io::Read,
    {
        let brdr = std::io::BufReader::new(rdr);
        let lines = std::io::BufRead::lines(brdr);
        let noerr = lines.map_while(Result::ok);
        self.lines2smaller(noerr)
    }

    #[cfg(feature = "std")]
    pub fn path2smaller<P>(&self, path: P) -> Result<SmallerRows, &'static str>
    where
        P: AsRef<std::path::Path>,
    {
        let f =
            std::fs::File::open(path).map_err(|_| "unable to open a smaller row set json file")?;
        Ok(self.read2smaller(f))
    }
}

impl<L, S, M> MergeJoined<L, S, M>
where
    L: LargerToKey,
{
    pub fn larger2joined(&mut self, larger: &[u8], s: &SmallerRows) -> Option<Joined> {
        let ol: Option<LargerRow> = serde_json::from_slice(larger).ok();
        ol.and_then(|l| self.larger2key.to_joined(l, s))
    }
}

impl<L, S, M> MergeJoined<L, S, M>
where
    L: LargerToKey,
    M: Merge,
{
    pub fn larger2merged(&mut self, larger: &[u8], s: &SmallerRows) -> Map<String, Value> {
        let o: Option<Joined> = self.larger2joined(larger, s);
        o.map(|j| {
            let l: LargerRow = j.larger;
            let s: SmallerRow = j.smaller;
            self.merger.merge(l, s)
        })
        .unwrap_or_default()
    }

    #[cfg(feature = "std")]
    pub fn lines2writer<I, W>(
        &mut self,
        larger: I,
        mut writer: W,
        s: &SmallerRows,
    ) -> Result<u64, &'static str>
    where
        I: Iterator<Item = String>,
        W: std::io::Write,
    {
        let mut merged_rows = larger.map(|l: String| {
            let ljson: &[u8] = l.as_bytes();
            self.larger2merged(ljson, s)
        });
        let cnt: u64 = merged_rows.try_fold(0, |state, next| {
            serde_json::to_writer(&mut writer, &next)
                .map_err(|_| "unable to serialize a merged row")?;
            writeln!(writer)
                .map_err(|_| "unable to write a delimiter")
                .map(|_| state + 1)
        })?;
        writer.flush().map_err(|_| "unable to flush").map(|_| cnt)
    }

    #[cfg(feature = "std")]
    pub fn read2writer<R, W>(
        &mut self,
        larger: R,
        writer: W,
        s: &SmallerRows,
    ) -> Result<u64, &'static str>
    where
        R: std::io::Read,
        W: std::io::Write,
    {
        let brdr = std::io::BufReader::new(larger);
        let lines = std::io::BufRead::lines(brdr);
        let noerr = lines.map_while(Result::ok);
        self.lines2writer(noerr, writer, s)
    }
}

#[cfg(feature = "std")]
pub fn large_jsons2writer<R, W, L, S, M>(
    mj: &mut MergeJoined<L, S, M>,
    larger: R,
    writer: W,
    s: &SmallerRows,
) -> Result<u64, &'static str>
where
    R: std::io::Read,
    W: std::io::Write,
    L: LargerToKey,
    S: SmallerToKey,
    M: Merge,
{
    mj.read2writer(larger, writer, s)
}

/// A row of a smaller row set(e.g, table)
#[derive(Default, Clone, Serialize, Deserialize)]
pub struct SmallerRow(Map<String, Value>);

/// A row of a larger row set(e.g, table)
#[derive(Default, Serialize, Deserialize)]
pub struct LargerRow(Map<String, Value>);

/// A joined row(a [`LargerRow`] and a [`SmallerRow`]).
#[derive(Default, Serialize, Deserialize)]
pub struct Joined {
    pub larger: LargerRow,
    pub smaller: SmallerRow,
}

/// A map of all rows of a smaller row set(e.g, table).
pub struct SmallerRows(pub BTreeMap<String, SmallerRow>);

/// Gets a key of a [`SmallerRow`].
pub trait SmallerToKey {
    /// Gets a primary key of a [`SmallerRow`] as [`String`].
    fn to_key(&self, s: &SmallerRow) -> String;

    /// Creates a map from smaller rows.
    fn rows2map<I>(&self, rows: I) -> SmallerRows
    where
        I: Iterator<Item = SmallerRow>,
    {
        let pairs = rows.map(|s: SmallerRow| {
            let key: String = self.to_key(&s);
            (key, s)
        });
        let m: BTreeMap<String, SmallerRow> = BTreeMap::from_iter(pairs);
        SmallerRows(m)
    }
}

/// Gets a key of a [`LargerRow`].
pub trait LargerToKey {
    /// Gets a primary key of a [`LargerRow`] as [`&str`].
    fn to_key_str(&mut self, s: &LargerRow) -> &str;

    /// Tries to create a joined row [`Joined`].
    fn to_joined(&mut self, l: LargerRow, s: &SmallerRows) -> Option<Joined> {
        let key: &str = self.to_key_str(&l);
        let srow: Option<&SmallerRow> = s.0.get(key);
        srow.map(|row| Joined {
            larger: l,
            smaller: row.clone(),
        })
    }
}

/// Joins a json row of a larger row set and a smaller row set.
///
/// # Arguments
/// - larger: A json row of a larger row set.
/// - s: A smaller row set.
/// - l2k: Gets a key from a row of a larger row set.
///
/// # Examples
///
/// ```rust
/// use rs_json_join::flat::mem::keystr::simple::{
///     SmallerRows,
///     Smaller2key,
///     SmallerToKey,
///     Joined,
///     LargerRow,
///     SmallerRow,
///     Larger2key,
/// };
/// use rs_json_join::flat::mem::keystr::simple;
///
/// let larger: &[u8] = r#"{"seqno":1, "user_id": 42}"#.as_bytes();
/// let smaller = vec![
///     r#"{"id": 42, "name": "JD"}"#.as_bytes(),
///     r#"{"id": 43, "name": "DJ"}"#.as_bytes(),
/// ];
/// let parsed = smaller.iter().flat_map(|s| {
///     serde_json::from_slice::<SmallerRow>(s).ok()
/// });
/// let val2str = simple::val2str_default();
/// let s2k: Smaller2key<_> = Smaller2key::new_default(val2str);
///
/// let val2wtr = simple::val2wtr_default();
/// /// LargerToKey
/// let mut l2k: Larger2key<_> = Larger2key::new_default(val2wtr).with_key("user_id".into());
///
/// let srows: SmallerRows = s2k.rows2map(parsed);
/// let joined: Joined = simple::larger2joined(larger, &srows, &mut l2k).unwrap_or_default();
/// let l: LargerRow = joined.larger;
/// let s: SmallerRow = joined.smaller;
/// let lj: String = serde_json::to_string(&l).unwrap_or_default();
/// let sj: String = serde_json::to_string(&s).unwrap_or_default();
/// assert_eq!(lj.as_str(), r#"{"seqno":1,"user_id":42}"#);
/// assert_eq!(sj.as_str(), r#"{"id":42,"name":"JD"}"#);
/// ```
pub fn larger2joined<L>(larger: &[u8], s: &SmallerRows, l2k: &mut L) -> Option<Joined>
where
    L: LargerToKey,
{
    serde_json::from_slice(larger)
        .ok()
        .and_then(|l: LargerRow| l2k.to_joined(l, s))
}

/// Creates a single [`Map`] from a [`LargerRow`] and a [`SmallerRow`].
pub trait Merge {
    fn merge(&self, l: LargerRow, s: SmallerRow) -> Map<String, Value>;
}

/// Merges a [`LargerRow`] and a [`SmallerRow`] using a key name map.
pub struct MergeSmallerKeyMap {
    /// A rename map to rename a key of a [`SmallerRow`] before a merge.
    pub smaller_keys_map: BTreeMap<String, String>,
}

impl Merge for MergeSmallerKeyMap {
    fn merge(&self, l: LargerRow, mut s: SmallerRow) -> Map<String, Value> {
        let pairs = self.smaller_keys_map.iter().flat_map(|kv| {
            let (key, val) = kv;
            let k: &str = key.as_str();
            let o: Option<_> = s.0.remove(k);
            let renamed: String = val.into();
            o.map(|v: Value| (renamed, v))
        });
        let mut m: Map<String, Value> = l.0;
        m.extend(pairs);
        m
    }
}

/// Creates a merged [`Map`] from a [`LargerRow`] and a [`SmallerRow`].
///
/// # Examples
///
/// ```rust
/// use std::collections::BTreeMap;
///
/// use serde_json::{Map, Value, json};
///
/// use rs_json_join::flat::mem::keystr::simple;
/// use rs_json_join::flat::mem::keystr::simple::{
///     LargerRow,
///     SmallerRow,
///     Merge,
///     MergeSmallerKeyMap,
/// };
///
/// let l: LargerRow = serde_json::from_slice(r#"{
///    "seqno": 1,
///    "user_id": 42
/// }"#.as_bytes()).unwrap_or_default();
///
/// let s: SmallerRow = serde_json::from_slice(r#"{
///    "id": 42,
///    "name": "JD"
/// }"#.as_bytes()).unwrap_or_default();
///
/// /// Merge
/// let merger = MergeSmallerKeyMap{
///     smaller_keys_map: BTreeMap::from([
///         ("id".into(), "uid".into()),
///         ("name".into(), "uname".into()),
///     ]),
/// };
/// let merged: Map<String, Value> = simple::to_merged(l, s, &merger);
///
/// let seqno: Value = merged.get("seqno").cloned().unwrap_or_default();
/// let user_id: Value = merged.get("user_id").cloned().unwrap_or_default();
/// let uid: Value = merged.get("uid").cloned().unwrap_or_default();
/// let uname: Value = merged.get("uname").cloned().unwrap_or_default();
/// assert_eq!(seqno, json!(1));
/// assert_eq!(user_id, json!(42));
/// assert_eq!(uid, json!(42));
/// assert_eq!(uname, json!("JD"));
/// ```
pub fn to_merged<M>(l: LargerRow, s: SmallerRow, merger: &M) -> Map<String, Value>
where
    M: Merge,
{
    merger.merge(l, s)
}

/// Converts a [`Value`] to a [`String`].
pub trait ValueToString {
    fn convert(&self, v: &Value) -> String;
}

/// Implements [`ValueToString`] by using format! macro.
pub struct Val2strJson {}
impl ValueToString for Val2strJson {
    fn convert(&self, v: &Value) -> String {
        format!("{v}")
    }
}

/// Creates default [`ValueToString`].
pub fn val2str_default() -> impl ValueToString {
    Val2strJson {}
}

/// Implements [`SmallerToKey`] using a key and a [`ValueToString`].
pub struct Smaller2key<V> {
    pub key: String,
    pub alt: String,
    pub val2str: V,
}

impl<V> Smaller2key<V>
where
    V: ValueToString,
{
    pub fn new_default(val2str: V) -> Self {
        Self {
            key: "id".into(),
            alt: "".into(),
            val2str,
        }
    }
    pub fn with_key(self, key: String) -> Self {
        Self {
            key,
            alt: self.alt,
            val2str: self.val2str,
        }
    }
}

impl<V> SmallerToKey for Smaller2key<V>
where
    V: ValueToString,
{
    fn to_key(&self, s: &SmallerRow) -> String {
        let val: Option<&Value> = s.0.get(self.key.as_str());
        val.map(|v| self.val2str.convert(v))
            .unwrap_or_else(|| self.alt.clone())
    }
}

/// Writes a [`Value`] to a [`core::fmt::Write`].
pub trait ValueToWriter {
    fn write<W>(&self, v: &Value, wtr: &mut W) -> Result<(), &'static str>
    where
        W: core::fmt::Write;
}

/// Implements [`ValueToWriter`] by using write! macro.
pub struct Val2wtrJson {}
impl ValueToWriter for Val2wtrJson {
    fn write<W>(&self, v: &Value, wtr: &mut W) -> Result<(), &'static str>
    where
        W: core::fmt::Write,
    {
        write!(wtr, "{v}").map_err(|_| "unable to write a value")
    }
}

/// Creates default [`ValueToWriter`].
pub fn val2wtr_default() -> impl ValueToWriter {
    Val2wtrJson {}
}

/// Implements [`LargerToKey`] using a key and a [`ValueToWriter`].
pub struct Larger2key<V> {
    pub key: String,
    pub alt: String,
    pub buf: String,
    pub val2wtr: V,
}

impl<V> Larger2key<V>
where
    V: ValueToWriter,
{
    pub fn new_default(val2wtr: V) -> Self {
        Self {
            key: "id".into(),
            alt: "".into(),
            buf: "00000000-0000-0000-0000-000000000000".into(),
            val2wtr,
        }
    }

    pub fn with_key(self, key: String) -> Self {
        Self {
            key,
            alt: self.alt,
            buf: self.buf,
            val2wtr: self.val2wtr,
        }
    }
}

impl<V> LargerToKey for Larger2key<V>
where
    V: ValueToWriter,
{
    fn to_key_str(&mut self, s: &LargerRow) -> &str {
        let val: Option<&Value> = s.0.get(self.key.as_str());
        val.and_then(|v| {
            self.buf.clear();
            self.val2wtr
                .write(v, &mut self.buf)
                .ok()
                .map(|_| self.buf.as_str())
        })
        .unwrap_or(self.alt.as_str())
    }
}
