extern crate crabquery;

use crabquery::*;

#[test]
fn test_docs_rs_index() {
    let document = Document::from(include_str!("fixtures/docs_rs.html"));

    let els = document.select("div.pure-u-sm-4-24");
    assert_eq!(els.len(), 15);

    let els = document.select(".pure-u-sm-4-24");
    assert_eq!(els.len(), 15);

    let els = document.select("meta[name=\"generator\"]");
    assert_eq!(els.len(), 1);

    let els = document.select("a");
    assert!(els.len() > 20);

    let els = document.select("a[href]");
    assert!(els.len() > 20);
}

#[test]
fn test_dungeon_majesty_index() {
    let document = Document::from(include_str!("fixtures/dungeon_majesty.html"));

    let els = document.select("div img.wp-manga-chapter-img");
    assert_eq!(els.len(), 18);
}