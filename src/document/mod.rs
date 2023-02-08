//! This module provides functionality for parsing and working with DomTree
//!
//! Supported selectors are:
//! * tag based `span` or `a`
//! * class based `.button`
//! * id based `#main_button`
//! * direct child `>`
//! * attribute selectors `[href]`, `[href="specific-value"]`, `[href*="contains-str"]`,
//! `[href^="begins-with"]`,, `[href$="ends-with"]`
//! * all combinations of above like `div.container > form#feedback input.button`
//!
use html5ever::driver::ParseOpts;
use html5ever::parse_document;
use html5ever::tendril::TendrilSink;
use html5ever::tree_builder::TreeBuilderOpts;
use markup5ever::{Attribute, QualName};
use markup5ever_arcdom::{ArcDom, Handle, NodeData};
use regex::{Captures, Regex};
use std::cell::{Ref, RefCell};
use std::collections::{HashMap, HashSet};
use std::default::Default;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

pub trait Selectable {
    fn select(&self, selector: &str) -> Vec<Element>;
}

pub struct Document {
    doc: ArcDom,
}

impl Debug for Document {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Document")
            .field("document", &self.doc.document)
            .finish()
    }
}

fn default_parse_opts() -> ParseOpts {
    ParseOpts {
        tree_builder: TreeBuilderOpts {
            drop_doctype: true,
            ..Default::default()
        },
        ..Default::default()
    }
}

impl From<&str> for Document {
    /// Create document from a string slice
    fn from(input: &str) -> Self {
        let doc = parse_document(ArcDom::default(), default_parse_opts())
            .from_utf8()
            .read_from(&mut input.as_bytes())
            .expect("could not parse html input");

        Self { doc }
    }
}

impl From<String> for Document {
    /// Create document from String
    fn from(input: String) -> Self {
        Self::from(input.as_str())
    }
}

impl Selectable for Document {
    /// Select elements using given css selector
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<span>hi there</span>");
    /// let sel = doc.select("span");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.text().unwrap(), "hi there");
    /// ```
    fn select(&self, selector: &str) -> Vec<Element> {
        let mut elements = vec![];
        for selector in selector.split(",") {
            let sel = Selector::from(selector.trim());
            let mut found = sel.find(self.doc.document.children.borrow());
            elements.append(&mut found);
        }
        elements
    }
}

impl Selectable for &Document {
    fn select(&self, selector: &str) -> Vec<Element> {
        (*self).select(selector)
    }
}

impl Selectable for &Element {
    fn select(&self, selector: &str) -> Vec<Element> {
        (*self).select(selector)
    }
}

#[derive(Debug, PartialEq, Clone)]
enum PseudoSpec {
    /// Implementation of [:empty] selector
    Empty,
    /// Implementation of [:not-empty] selector
    NotEmpty,
    /// Implementation of [:not(selector)] selector
    Not(Selector),
    /// Implementation of [:has(selector)] selector
    Has(Selector),
    /// Implementation of [:contains("value")] selector
    Contains(String),
    /// Implementation of [:icontains("value")] selector
    CaseInsensitiveContains(String),
}

impl PseudoSpec {
    fn matches(&self, node: &Arc<markup5ever_arcdom::Node>) -> bool {
        use PseudoSpec::*;

        let children = node.children.borrow();

        let texts = children
            .iter()
            .filter(|node| {
                if let NodeData::Text { contents: _ } = node.data {
                    return true;
                } else {
                    return false;
                }
            })
            .map(|text_node| {
                if let NodeData::Text { contents } = &text_node.data {
                    return contents.borrow();
                } else {
                    unreachable!();
                }
            });

        match self {
            Not(selector) => selector.find(children).is_empty(),
            Has(selector) => !selector.find(children).is_empty(),
            Empty => children.is_empty(),
            NotEmpty => !children.is_empty(),
            Contains(v) => {
                let mut found = false;
                for text in texts {
                    if text.contains(v) {
                        found = true;
                        break;
                    }
                }
                return found;
            }
            CaseInsensitiveContains(v) => {
                let mut found = false;
                for text in texts {
                    if text.to_ascii_lowercase().contains(v) {
                        found = true;
                        break;
                    }
                }
                return found;
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum AttributeSpec {
    /// Implementation of [attribute] selector
    Present,
    /// Implementation of [attribute="value"] selector
    Exact(String),
    /// Implementation of [attribute^="value"] selector
    Starts(String),
    /// Implementation of [attribute$="value"] selector
    Ends(String),
    /// Implementation of [attribute*="value"] selector
    Contains(String),
}

impl AttributeSpec {
    fn matches(&self, other: String) -> bool {
        use AttributeSpec::*;

        match self {
            Present => true,
            Exact(v) => &other == v,
            Starts(v) => other.starts_with(v),
            Ends(v) => other.ends_with(v),
            Contains(v) => other.contains(v),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct Matcher {
    tag: Vec<String>,
    class: Vec<String>,
    id: Vec<String>,
    attribute: HashMap<String, AttributeSpec>,
    pseudo_selector: Vec<PseudoSpec>,
    direct_match: bool,
    adjacent_sibling: bool,
    siblings: bool,
}

impl From<String> for Matcher {
    fn from(input: String) -> Self {
        Self::from(input.as_str())
    }
}

impl From<&str> for Matcher {
    fn from(input: &str) -> Self {
        let mut segments = vec![];
        let mut buf = "".to_string();
        let mut nested_level = 0;

        for c in input.chars() {
            match c {
                '>' | '+' | '~' => {
                    if nested_level == 0 {
                        return Self {
                            tag: vec![],
                            class: vec![],
                            id: vec![],
                            attribute: HashMap::new(),
                            direct_match: c == '>',
                            siblings: c == '~',
                            adjacent_sibling: c == '+',
                            pseudo_selector: vec![],
                        };
                    }
                }
                '#' | '.' | '[' | ':' => {
                    if nested_level == 0 {
                        if c == '[' {
                            nested_level += 1;
                        }
                        segments.push(buf);
                        buf = "".to_string();
                    }
                }
                '(' => {
                    nested_level += 1;
                }
                ']' | ')' => {
                    nested_level -= 1;
                    if nested_level == 0 {
                        segments.push(buf);
                        buf = "".to_string();
                        continue;
                    }
                }
                _ => {}
            };

            buf.push(c);
        }
        segments.push(buf);

        let mut res = Self {
            tag: vec![],
            class: vec![],
            id: vec![],
            attribute: HashMap::new(),
            direct_match: false,
            adjacent_sibling: false,
            siblings: false,
            pseudo_selector: vec![],
        };

        for segment in segments {
            match segment.chars().next() {
                Some('#') => res.id.push(segment[1..].to_string()),
                Some('.') => res.class.push(segment[1..].to_string()),
                Some('[') => res.add_data_attribute(segment[1..].to_string()),
                Some(':') => res.add_pseudo_selector(segment[1..].to_string()),
                None => {}
                _ => res.tag.push(segment),
            }
        }

        res
    }
}

impl Matcher {
    fn add_pseudo_selector(&mut self, spec: String) {
        use PseudoSpec::*;

        let parts = spec.split_once('(');

        if let Some((name, value)) = parts {
            let value = value.trim_matches(|c| c == '\'' || c == '"');

            match name {
                "contains" => self.pseudo_selector.push(Contains(value.to_owned())),
                "icontains" => self.pseudo_selector.push(CaseInsensitiveContains(
                    value.to_ascii_lowercase().to_owned(),
                )),
                "has" => self.pseudo_selector.push(Has(value.into())),
                "not" => self.pseudo_selector.push(Not(value.into())),
                _ => {}
            }
        } else {
            match spec.as_str() {
                "empty" => self.pseudo_selector.push(Empty),
                "not-empty" => self.pseudo_selector.push(NotEmpty),
                _ => {}
            }
        }
    }

    fn add_data_attribute(&mut self, spec: String) {
        use AttributeSpec::*;

        let parts = spec.split('=').collect::<Vec<_>>();

        if parts.len() == 1 {
            let k = parts[0];
            self.attribute.insert(k.to_string(), Present);
            return;
        }

        let v = parts[1].trim_matches(|c| c == '"' || c == '\'').to_string();
        let k = parts[0];
        let k = k[..k.len() - 1].to_string();

        match parts[0].chars().last() {
            Some('^') => {
                self.attribute.insert(k, Starts(v));
            }
            Some('$') => {
                self.attribute.insert(k, Ends(v));
            }
            Some('*') => {
                self.attribute.insert(k, Contains(v));
            }
            Some(_) => {
                let k = parts[0].to_string();
                self.attribute.insert(k, Exact(v));
            }
            None => {
                panic!("Could not parse attribute spec \"{}\"", spec);
            }
        }
    }

    fn pseudo_match(&self, node: &Arc<markup5ever_arcdom::Node>) -> bool {
        for pseudo_selector in self.pseudo_selector.iter() {
            if !pseudo_selector.matches(node) {
                return false;
            }
        }
        return true;
    }

    fn matches(&self, name: &QualName, attrs: Ref<'_, Vec<Attribute>>) -> bool {
        let mut id_match = self.id.is_empty();
        if let Some(el_id) = get_attr(&attrs, "id") {
            let el_ids: Vec<_> = el_id.split_whitespace().collect();
            id_match = self.id.iter().all(|id| el_ids.iter().any(|eid| eid == id))
        }

        let mut class_match = self.class.is_empty();
        if let Some(el_class) = get_attr(&attrs, "class") {
            let el_classes: Vec<_> = el_class.split_whitespace().collect();

            class_match = self
                .class
                .iter()
                .all(|class| el_classes.iter().any(|eclass| eclass == class))
        }

        let mut attr_match = true;
        for (k, v) in &self.attribute {
            if let Some(value) = get_attr(&attrs, k.as_str()) {
                if !v.matches(value) {
                    attr_match = false;
                    break;
                }
            } else {
                attr_match = false;
                break;
            }
        }

        let name = name.local.to_string();
        let tag_match =
            self.tag.is_empty() || self.tag.iter().any(|tag| tag == "*" || &name == tag);

        tag_match && id_match && class_match && attr_match
    }
}

#[derive(Debug, PartialEq, Clone)]
struct Selector {
    matchers: Vec<Matcher>,
}

lazy_static! {
    static ref REGEX_BETWEEN_BRACKETS: Regex = Regex::new(r"\(([^)]*)\)").unwrap();
    static ref REGEX_NEED_SPACES: Regex = Regex::new(r"\s*([>+~])\s*").unwrap();
}

const TMP_SPACE_REPLACEMENT: &str = "$$%#%@^*&!#";

impl From<&str> for Selector {
    fn from(input: &str) -> Self {
        let input = REGEX_NEED_SPACES.replace_all(input.trim(), |caps: &Captures| {
            format!(" {} ", caps[1].to_string())
        });
        let input = REGEX_BETWEEN_BRACKETS.replace_all(input.trim(), |caps: &Captures| {
            caps[0].replace(" ", TMP_SPACE_REPLACEMENT)
        });
        let matchers: Vec<_> = input
            .split_whitespace()
            .map(|matcher| Matcher::from(matcher.replace(TMP_SPACE_REPLACEMENT, " ")))
            .collect();

        Selector { matchers }
    }
}

fn get_attr(attrs: &Ref<'_, Vec<Attribute>>, name: &str) -> Option<String> {
    attrs
        .iter()
        .filter(|attr| &attr.name.local == name)
        .take(1)
        .map(|attr| attr.value.to_string())
        .collect::<Vec<_>>()
        .pop()
}

impl Selector {
    fn find_nodes(
        &self,
        matcher: &Matcher,
        elements: Vec<Handle>,
        direct_match: bool,
    ) -> Vec<Handle> {
        let mut accumulate = vec![];

        for element in elements.iter() {
            if !direct_match {
                let children: Vec<_> = element.children.borrow().iter().map(Arc::clone).collect();
                accumulate.append(&mut self.find_nodes(matcher, children, false));
            }
            match element.data {
                NodeData::Element {
                    ref name,
                    ref attrs,
                    ..
                } if matcher.matches(name, attrs.borrow()) => {
                    if matcher.pseudo_match(element) {
                        accumulate.push(Arc::clone(&element));
                    }
                }
                _ => {}
            };
        }

        accumulate
    }

    fn find(&self, elements: Ref<'_, Vec<Handle>>) -> Vec<Element> {
        let mut elements: Vec<_> = elements.iter().map(Arc::clone).collect();
        let mut direct_match = false;

        for (index, matcher) in self.matchers.iter().enumerate() {
            // Get adjacent sibling
            if matcher.adjacent_sibling || matcher.siblings {
                direct_match = true;
                elements = elements
                    .into_iter()
                    .flat_map(|mut el| {
                        // Must have a parent to get the siblings
                        if let Some(weak_parent) = el.parent.take() {
                            let mut parent = weak_parent.upgrade().map(Element::from);
                            el.parent.set(Some(weak_parent));

                            if index == 0 {
                                parent = parent.map_or(None, |parent| {
                                    el = parent.handle.clone();
                                    parent.parent()
                                });
                            }

                            if let Some(parent) = parent {
                                let children = parent.handle.children.borrow();
                                // Get only the element nodes
                                let children: Vec<&Arc<markup5ever_arcdom::Node>> = children
                                    .iter()
                                    .filter(|el| {
                                        if let NodeData::Element { .. } = el.data {
                                            return true;
                                        }
                                        return false;
                                    })
                                    .collect();
                                // Get the position of the current node inside of the children vector
                                let position = children.iter().position(|element| {
                                    // Use pointers to compare, because PartialEq is not implemented for Arc<Node>
                                    let ptr1 = &el.children as *const _ as *const usize;
                                    let ptr2 = &element.children as *const _ as *const usize;

                                    return ptr1 == ptr2;
                                });

                                // If a position is found
                                if let Some(position) = position {
                                    // Sibling is next child
                                    let sibling = position + 1;
                                    // If there is a sibling
                                    if sibling < children.len() {
                                        if matcher.adjacent_sibling {
                                            // Get the adjacent sibling
                                            return vec![Arc::clone(
                                                children.get(sibling).unwrap(),
                                            )];
                                        } else {
                                            // Get the adjacent siblings
                                            let siblings = children[sibling..]
                                                .iter()
                                                .map(|node| Arc::clone(node))
                                                .collect::<Vec<Arc<markup5ever_arcdom::Node>>>();
                                            return siblings;
                                        }
                                    }
                                }
                            }
                        }
                        return vec![];
                    })
                    .collect();
                continue;
            } else if matcher.direct_match {
                direct_match = true;
                if index != 0 {
                    elements = elements
                        .iter()
                        .flat_map(|el| {
                            el.children
                                .borrow()
                                .iter()
                                .map(Arc::clone)
                                .collect::<Vec<_>>()
                        })
                        .collect();
                }
                continue;
            }

            elements = self.find_nodes(matcher, elements, direct_match);
            direct_match = false;
        }

        for element in elements.iter() {
            println!("found {:?}", Element::from(element).attr("class"));
        }
        let elements: Vec<Element> = elements.into_iter().map(Element::from).collect();
        let v: HashSet<_> = elements.into_iter().collect();
        return v.into_iter().collect();
    }
}

#[derive(Clone, Debug)]
pub struct Element {
    handle: Handle,
}

impl Hash for Element {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr = &self.handle.children as *const _ as *const usize;
        ptr.hash(state);
    }
}

impl PartialEq for Element {
    fn eq(&self, other: &Self) -> bool { 
        let ptr1 = &self.handle.children as *const _ as *const usize;
        let ptr2 = &other.handle.children as *const _ as *const usize;
        return ptr1 == ptr2;
    }
}

impl Eq for Element {}

impl From<Handle> for Element {
    fn from(e: Handle) -> Self {
        Self::from(&e)
    }
}

impl From<&Handle> for Element {
    fn from(e: &Handle) -> Self {
        Element {
            handle: Arc::clone(e),
        }
    }
}

impl Selectable for Element {
    /// Select child elements using given css selector
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<span><a class='link'>hi there</a></span>");
    /// let sel = doc.select("span");
    /// let el = sel.first().unwrap();
    /// let sel = el.select("a");
    /// let a = sel.first().unwrap();
    ///
    /// assert_eq!(a.attr("class").unwrap(), "link");
    /// ```
    fn select(&self, selector: &str) -> Vec<Element> {
        let mut elements = vec![];
        for selector in selector.split(",") {
            let sel = Selector::from(selector.trim());
            let mut found = sel.find(self.handle.children.borrow());
            elements.append(&mut found);
        }
        elements
    }
}

impl Element {
    /// Get value of an attribute
    ///
    /// # Arguments
    /// * `name` - attribute name
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<a class='link'>hi there</a>");
    /// let sel = doc.select("a");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.attr("class").unwrap(), "link");
    /// ```
    pub fn attr(&self, name: &str) -> Option<String> {
        match self.handle.data {
            NodeData::Element { ref attrs, .. } => get_attr(&attrs.borrow(), name),
            _ => None,
        }
    }

    /// Get tag value
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<a class='link'>hi there</a>");
    /// let sel = doc.select("a");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.tag().unwrap(), "a");
    /// ```
    pub fn tag(&self) -> Option<String> {
        match self.handle.data {
            NodeData::Element { ref name, .. } => Some(name.local.to_string()),
            _ => None,
        }
    }

    /// Get text
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<a class='link'>hi there <span>crab</span></a>");
    /// let sel = doc.select("a");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.text().unwrap(), "hi there ");
    /// ```
    pub fn text(&self) -> Option<String> {
        let mut res = "".to_string();
        let children = self.handle.children.borrow();

        for child in children.iter() {
            if let NodeData::Text { ref contents } = child.data {
                res.push_str(&contents.borrow().to_string().as_str());
            }
        }

        return if res.is_empty() { None } else { Some(res) };
    }

    /// Get text from this and all child nodes
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<a class='link'>hi there <span>crab</span></a>");
    /// let sel = doc.select("a");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.all_text().unwrap(), "hi there crab");
    /// ```
    pub fn all_text(&self) -> Option<String> {
        let mut res = "".to_string();
        let children = self.handle.children.borrow();

        for child in children.iter() {
            if let NodeData::Text { ref contents } = child.data {
                res.push_str(&contents.borrow().to_string().as_str());
            } else if let NodeData::Element { .. } = child.data {
                res.push_str(
                    Element::from(child)
                        .all_text()
                        .unwrap_or(String::new())
                        .as_str(),
                );
            }
        }

        return if res.is_empty() { None } else { Some(res) };
    }

    /// Get children elements
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<a class='link'><span>hi there</span></a>");
    /// let sel = doc.select("a");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.children().first().unwrap().text().unwrap(), "hi there");
    /// ```
    pub fn children(&self) -> Vec<Element> {
        self.handle
            .children
            .borrow()
            .iter()
            .filter(|n| {
                if let NodeData::Element { .. } = n.data {
                    true
                } else {
                    false
                }
            })
            .map(Element::from)
            .collect::<Vec<_>>()
    }

    /// Get parent element
    ///
    /// # Example
    /// ```
    /// use crabquery::Document;
    /// use crabquery::Selectable;
    ///
    /// let doc = Document::from("<a class='link'><span>hi there</span></a>");
    /// let sel = doc.select("span");
    /// let el = sel.first().unwrap();
    ///
    /// assert_eq!(el.parent().unwrap().tag().unwrap(), "a");
    /// ```
    pub fn parent(&self) -> Option<Element> {
        if let Some(parent) = self.handle.parent.take() {
            let wrapper = parent.upgrade().map(Element::from);
            self.handle.parent.set(Some(parent));

            return wrapper;
        }

        None
    }
}

pub struct Elements {
    pub elements: Vec<Element>,
}

impl From<Vec<Element>> for Elements {
    fn from(elements: Vec<Element>) -> Self {
        Elements { elements }
    }
}

impl Elements {
    pub fn attrs(&self, attrs: Vec<&str>) -> Option<String> {
        let mut buff = String::new();

        for element in self.elements.iter() {
            for attr in attrs.iter() {
                if let Some(text) = element.attr(attr) {
                    buff += &text;
                    buff += "\n";
                }
                break;
            }
        }

        let text = buff.trim().to_string();

        return if text.is_empty() { None } else { Some(text) };
    }

    pub fn attr(&self, name: &str) -> Option<String> {
        let mut buff = String::new();

        for element in self.elements.iter() {
            if let Some(text) = element.attr(name) {
                buff += &text;
                buff += "\n";
            }
        }

        let text = buff.trim().to_string();

        return if text.is_empty() { None } else { Some(text) };
    }

    pub fn text(&self) -> Option<String> {
        let mut buff = String::new();

        for element in self.elements.iter() {
            if let Some(text) = element.text() {
                buff += &text;
                buff += "\n";
            }
        }

        let text = buff.trim().to_string();

        return if text.is_empty() { None } else { Some(text) };
    }

    pub fn all_text(&self) -> Option<String> {
        let mut buff = String::new();

        for element in self.elements.iter() {
            if let Some(text) = element.all_text() {
                buff += &text;
                buff += "\n";
            }
        }

        let text = buff.trim().to_string();

        return if text.is_empty() { None } else { Some(text) };
    }

    pub fn select(&self, selector: &str) -> Vec<Element> {
        let mut elements = vec![];
        for selector in selector.split(",") {
            let sel = Selector::from(selector.trim());
            let mut found = sel.find(
                RefCell::new(
                    self.elements
                        .iter()
                        .map(|element| element.handle.clone())
                        .collect(),
                )
                .borrow(),
            );
            elements.append(&mut found);
        }
        elements
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Matcher tests
    #[test]
    fn test_matcher_tag() {
        let m = Matcher::from("a");
        assert_eq!(m.tag, vec!["a".to_string()],);
    }

    #[test]
    fn test_matcher_complex() {
        let m = Matcher::from("a.link.another_class#idofel.klass");
        assert_eq!(m.tag, vec!["a".to_string()]);
        assert_eq!(
            m.class,
            vec![
                "link".to_string(),
                "another_class".to_string(),
                "klass".to_string()
            ]
        );
        assert_eq!(m.id, vec!["idofel".to_string()]);
    }

    #[test]
    fn test_matcher_direct_match() {
        let m = Matcher::from(">");
        assert_eq!(m.direct_match, true);
    }

    #[test]
    fn test_matcher_data_attribute_present() {
        let m = Matcher::from("a[target]");
        let mut attr = HashMap::new();
        attr.insert("target".to_string(), AttributeSpec::Present);
        assert_eq!(m.attribute, attr);
    }

    #[test]
    fn test_matcher_data_attribute_exact() {
        let m = Matcher::from("a[target=\"_blank\"]");
        let mut attr = HashMap::new();
        attr.insert(
            "target".to_string(),
            AttributeSpec::Exact("_blank".to_string()),
        );
        assert_eq!(m.attribute, attr);
    }

    #[test]
    fn test_matcher_data_attribute_starts() {
        let m = Matcher::from("a[target^=\"_blank\"]");
        let mut attr = HashMap::new();
        attr.insert(
            "target".to_string(),
            AttributeSpec::Starts("_blank".to_string()),
        );
        assert_eq!(m.attribute, attr);
    }

    #[test]
    fn test_matcher_data_attribute_ends() {
        let m = Matcher::from("a[target$=\"_blank\"]");
        let mut attr = HashMap::new();
        attr.insert(
            "target".to_string(),
            AttributeSpec::Ends("_blank".to_string()),
        );
        assert_eq!(m.attribute, attr);
    }

    #[test]
    fn test_matcher_data_attribute_contains() {
        let m = Matcher::from("a[target*=\"_blank\"]");
        let mut attr = HashMap::new();
        attr.insert(
            "target".to_string(),
            AttributeSpec::Contains("_blank".to_string()),
        );
        assert_eq!(m.attribute, attr);
    }

    // Element tests
    #[test]
    fn test_el_tag() {
        let doc = Document::from("<a class='link'>hi there</a>");
        let sel = doc.select("a");
        let el = sel.first().unwrap();
        assert_eq!(el.tag(), Some("a".to_string()));
    }

    #[test]
    fn test_el_attr_class() {
        let doc = Document::from("<a class='link'>hi there</a>");
        let sel = doc.select("a");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("class"), Some("link".to_string()));
    }

    #[test]
    fn test_el_attr_id() {
        let doc = Document::from("<a class='link' id=linkilink>hi there</a>");
        let sel = doc.select("a");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("id"), Some("linkilink".to_string()));
    }

    #[test]
    fn test_el_attr_double_id() {
        let doc = Document::from("<a class='link' id='linkone linkmain'>hi there</a>");
        let sel = doc.select("a#linkone#linkmain");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("class"), Some("link".to_string()));
    }

    #[test]
    fn test_el_attr_double_class() {
        let doc = Document::from("<a class='link button' id='linkmain'>hi there</a>");
        let sel = doc.select("a.link.button");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("id"), Some("linkmain".to_string()));
    }

    #[test]
    fn test_el_attr_double_class_reverse_order() {
        let doc = Document::from("<a class='link button' id='linkmain'>hi there</a>");
        let sel = doc.select("a.button.link");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("id"), Some("linkmain".to_string()));
    }

    #[test]
    fn test_el_nested_selection() {
        let doc = Document::from(
            "<div class='container'><a class='link button' id='linkmain'>hi there</a></div>",
        );
        let sel = doc.select("div.container a.button.link");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("id"), Some("linkmain".to_string()));
    }

    #[test]
    fn test_el_nested_selection_with_el_in_between() {
        let doc = Document::from(
            "<div class='container'><span>text</span><a class='link button' id='linkmain'>hi there</a></div>",
        );
        let sel = doc.select("div.container a.button.link");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("id"), Some("linkmain".to_string()));
    }

    #[test]
    fn test_el_double_nested_selection() {
        let doc = Document::from(
            "<div class='container'><span>text<a class='link button' id='linkmain'>hi there</a></span></div>",
        );
        let sel = doc.select("div.container a.button.link");
        let el = sel.first().unwrap();
        assert_eq!(el.attr("id"), Some("linkmain".to_string()));
    }

    #[test]
    fn test_el_double_nested_direct_child_no_match() {
        let doc = Document::from(
            "<div class='container'><span>text<a class='link button' id='linkmain'>hi there</a></span></div>",
        );
        let sel = doc.select("div.container > a.button.link");
        let el = sel.first();
        assert!(el.is_none());
    }

    #[test]
    fn test_el_double_nested_direct_child_match() {
        let doc = Document::from(
            "<div class='container'>
               <a class='link button' id='linkmain'>
                 <span>text hi there</span>
               </a>
             </div>",
        );
        let sel = doc.select("div.container > a.button.link");
        let el = sel.first();
        assert!(el.is_some());
    }

    #[test]
    fn test_simple_multiple_a() {
        let doc = Document::from(
            "<div class='container'>
               <a class='link button' id='linkmain'>
                 <span>text hi there</span>
               </a>
               <span>text hi there <a href='blob'>two</a></span>
             </div>",
        );
        let sel = doc.select("a");
        assert_eq!(sel.len(), 2);
    }

    #[test]
    fn test_simple_multiple_a_in_div() {
        let doc = Document::from(
            "<div class='container'>
               <a class='link button' id='linkmain'>
                 <span>text hi there</span>
               </a>
             </div>
             <div>
               <span>text hi there
                 <a class='blob'>two</a>
               </span>
             </div>
             ",
        );
        let sel = doc.select("div a");
        assert_eq!(sel.len(), 2);
    }

    #[test]
    fn test_simple_attribute_present() {
        let doc = Document::from(
            "<div>
               <span>text hi there
                 <a data-counter='blob'>two</a>
               </span>
             </div>",
        );
        let sel = doc.select("div > span > a[data-counter]");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_simple_attribute_starts() {
        let doc = Document::from(
            "<div>
               <span>text hi there
                 <a data-counter='blobovo'>two</a>
               </span>
             </div>",
        );
        let sel = doc.select("div > span > a[data-counter^=\"blob\"]");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_simple_attribute_ends() {
        let doc = Document::from(
            "<div>
               <span>text hi there
                 <a data-counter='blobovo'>two</a>
               </span>
             </div>",
        );
        let sel = doc.select("div > span > a[data-counter$=\"ovo\"]");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_simple_attribute_contains() {
        let doc = Document::from(
            "<div>
               <span>text hi there
                 <a data-counter='blobovo'>two</a>
               </span>
             </div>",
        );
        let sel = doc.select("div > span > a[data-counter*=\"obo\"]");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_simple_text() {
        let doc = Document::from("<span>text hi there</span>");
        let sel = doc.select("span");
        let el = sel.first().unwrap();
        assert_eq!(el.text().unwrap(), "text hi there".to_string());
    }

    #[test]
    fn test_el_children() {
        let doc = Document::from(
            "<div>
            <span>one</span>
            <span>two</span>
            <span>three</span>
            </div>",
        );
        let sel = doc.select("div");
        let el = sel.first().unwrap();
        assert_eq!(el.children().len(), 3);
        assert_eq!(el.children().first().unwrap().text().unwrap(), "one");
    }

    #[test]
    fn test_el_parent() {
        let doc = Document::from(
            "<div>
            <span>one</span>
            </div>",
        );
        let sel = doc.select("span");
        let el = sel.first().unwrap();
        assert!(el.parent().is_some());
        assert_eq!(el.parent().unwrap().tag().unwrap(), "div");
    }

    #[test]
    fn test_only_id() {
        let doc = Document::from(
            "<div>
            <span>one</span>
            <span id=\"two\">two</span>
            </div>",
        );
        let sel = doc.select("#two");
        let el = sel.first().unwrap();
        assert!(el.parent().is_some());
        assert_eq!(el.parent().unwrap().tag().unwrap(), "div");
    }

    #[test]
    fn test_attribute_selection_multiple_els() {
        let doc = Document::from(
            "<head>
                <meta property='og:title' content='content'/>
                <meta content='content'/>
            </head>",
        );
        let sel = doc.select("meta[property=\"og:title\"]");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_pseudo_selector_contains() {
        let doc = Document::from(
            "<div>
                <span>one</span>
                <span>One</span>
                <script>
                    var owo = 0;
                </script>
                <script src=\"myscripts.js\"></script>
            </div>",
        );
        let sel = doc.select("span:contains('one')");
        assert_eq!(sel.len(), 1);
        let sel = doc.select("span:icontains('one')");
        assert_eq!(sel.len(), 2);
        let sel = doc.select("script:contains(owo)");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_pseudo_selector_has() {
        let doc = Document::from(
            "<div>
                <span class=\"owo\">one</span>
            </div>",
        );
        let sel = doc.select("div:has(span.owo:contains(one))");
        assert_eq!(sel.len(), 1);

        let sel = doc.select("div:has(span.owo:contains(two))");
        assert_eq!(sel.len(), 0);
    }

    #[test]
    fn test_pseudo_selector_not() {
        let doc = Document::from(
            "<div>
                <span class=\"owo\">one</span>
                <span class=\"uwu\">two</span>
            </div>",
        );
        let sel = doc.select("div:not(span.owo:contains(one))");
        assert_eq!(sel.len(), 0);

        let sel = doc.select("div:not(span:contains(three)):has(span.uwu)");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_pseudo_selector_empty() {
        let doc = Document::from(
            "<div>
                <h1>Not Empty</h1>
                <h1></h1>
                <h1><span>Not Empty</span></h1>
            </div>",
        );
        let sel = doc.select("h1:empty");
        assert_eq!(sel.len(), 1);

        let sel = doc.select("h1:not-empty");
        assert_eq!(sel.len(), 2);
    }

    #[test]
    fn test_adjacent_sibling() {
        let doc = Document::from(
            "<div>
                <h1>one</h1>
                <h2>two</h2>
                <h3>three</h3>
                <div>
                    <span>four</span>
                    <span>five</span>
                    <span>six</span>
                </div>
                <div>
                    <span>four</span>
                    <span>five</span>
                    <span>six</span>
                </div>
            </div>",
        );
        let sel = doc.select("h1 + h2");
        assert_eq!(sel.len(), 1);
        assert_eq!(sel.first().unwrap().tag(), Some("h2".to_owned()));

        let sel = doc.select("h1 + h3");
        assert_eq!(sel.len(), 0);

        let sel = doc.select("div > div span:contains(five) + span");
        assert_eq!(sel.len(), 2);
        assert_eq!(sel.first().unwrap().text(), Some("six".to_owned()));
        assert_eq!(sel.last().unwrap().text(), Some("six".to_owned()));
    }

    #[test]
    fn test_siblings() {
        let doc = Document::from(
            "<div>
                <h1>one</h1>
                <h2>two</h2>
                <h3>three</h3>
                <div>
                    <span>four</span>
                    <span>five</span>
                    <span>six</span>
                </div>
                <div>
                    <span>four</span>
                    <span>five</span>
                    <span>six</span>
                </div>
            </div>",
        );
        let sel = doc.select("h1 ~ h2");
        assert_eq!(sel.len(), 1);
        assert_eq!(sel.first().unwrap().tag(), Some("h2".to_owned()));

        let sel = doc.select("h1 ~ h3");
        assert_eq!(sel.len(), 1);
        assert_eq!(sel.first().unwrap().tag(), Some("h3".to_owned()));

        let sel = doc.select("h2 ~ h1");
        assert_eq!(sel.len(), 0);

        let sel = doc.select("div > div span:contains(four) ~ *:contains(six)");
        assert_eq!(sel.len(), 2);
        assert_eq!(sel.first().unwrap().text(), Some("six".to_owned()));
        assert_eq!(sel.last().unwrap().text(), Some("six".to_owned()));
    }

    #[test]
    fn test_pseudo_selector_nested() {
        let doc = Document::from(
            "<div>
                <div>
                    <span>
                        <div>nested</div>
                    </span>
                </div>
                <span>owo</span>
            </div>",
        );

        let sel = doc.select("div:has(> div:has(> span))");
        assert_eq!(sel.len(), 1);

        let sel = doc.select("div:has(> div:has(~ span))");
        assert_eq!(sel.len(), 1);
    }

    #[test]
    fn test_pseudo_selector_icontains() {
        let doc = Document::from(
            "<li>
                Genres :
                <a>poopoo</a>
            </li>",
        );

        let sel = doc.select("li:icontains(genre) > a");
        assert_eq!(sel.len(), 1);
    }
}
