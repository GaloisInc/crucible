use std::cmp;
use std::collections::{HashMap, HashSet};
use std::io::{self, Read};
use std::rc::Rc;
use regex::Regex;
use crate::{Context, Production, Nonterminal, ProductionId, NonterminalId, NonterminalRef, Chunk};

#[derive(Default)]
struct GrammarBuilder {
    prods: Vec<Production>,
    nts: Vec<Nonterminal>,

    nts_by_name: HashMap<String, NonterminalId>,
    text_interner: HashSet<Rc<str>>,
}

impl GrammarBuilder {
    pub fn nt_id(&mut self, name: &str) -> NonterminalId {
        if let Some(&id) = self.nts_by_name.get(name) {
            id
        } else {
            let id = self.nts.len();
            self.nts.push(Nonterminal::default());
            self.nts_by_name.insert(name.to_owned(), id);
            id
        }
    }

    pub fn add_prod(&mut self, nt: NonterminalId, prod: Production) {
        let id = self.prods.len();
        self.prods.push(prod);
        self.nts[nt].productions.push(id);
    }

    pub fn intern_text(&mut self, s: &str) -> Rc<str> {
        if let Some(x) = self.text_interner.get(s) {
            return x.clone();
        } else {
            let x: Rc<str> = s.into();
            self.text_interner.insert(x.clone());
            x
        }
    }

    fn parse_grammar(&mut self, lines: &[&str]) {
        struct PendingBlock {
            lhs: NonterminalId,
            start_line: usize,
            end_line: usize,
            min_indent: usize,
        }

        let mut cur_block: Option<PendingBlock> = None;
        for (i, line) in lines.iter().enumerate() {
            let trimmed = line.trim_start();
            if let Some(ref mut block) = cur_block {
                if trimmed.len() == 0 {
                    // Internal blank or all-whitespace are accepted, regardless of their
                    // indentation level.  However, we don't update `end_line`, so trailing blank
                    // lines after a block are ignored.
                    continue;
                }

                let indent = line.len() - trimmed.len();
                if indent > 0 {
                    // Include non-blank lines as long as they're indented by some amount.
                    block.min_indent = cmp::min(block.min_indent, indent);
                    block.end_line = i + 1;
                    continue;
                } else {
                    // The first non-indented line marks the end of the block.
                    let block = cur_block.take().unwrap();
                    let prod = self.parse_block(
                        block.start_line,
                        &lines[block.start_line .. block.end_line],
                        block.min_indent,
                    );
                    self.add_prod(block.lhs, prod);
                }
            }

            // We check this first so that all-whitespace lines are treated like blank ones instead of
            // raising an error.
            if trimmed.len() == 0 || line.starts_with("//") {
                continue;
            }

            if trimmed.len() < line.len() {
                eprintln!("line {}: error: found indented line outside block", i + 1);
                continue;
            }

            if let Some(delim) = line.find("::=") {
                let before = line[.. delim].trim();
                let after = line[delim + 3 ..].trim();
                let nt = self.nt_id(before);

                if after.len() == 0 {
                    // Start of a multi-line block
                    cur_block = Some(PendingBlock {
                        lhs: nt,
                        start_line: i + 1,
                        end_line: i + 1,
                        min_indent: usize::MAX,
                    });
                } else {
                    // Single-line case
                    let mut prod = Production::default();
                    self.parse_line(&mut prod, after, false);
                    self.add_prod(nt, prod);
                }
            } else {
                eprintln!("line {}: error: expected `::=`", i + 1);
                continue;
            }
        }

        if let Some(block) = cur_block {
            let prod = self.parse_block(
                block.start_line,
                &lines[block.start_line .. block.end_line],
                block.min_indent,
            );
            self.add_prod(block.lhs, prod);
        }
    }


    fn parse_block(
        &mut self,
        first_line: usize,
        lines: &[&str],
        indent: usize,
    ) -> Production {
        let marker_line_re = Regex::new(r"^(\s*)<<([a-zA-Z0-9_]+)>>$").unwrap();

        let mut prod = Production::default();
        for (i, line) in lines.iter().enumerate() {
            // The last line never gets a trailing newline.
            let newline = i < lines.len() - 1;

            if line.len() < indent {
                prod.chunks.push(Chunk::Text(self.intern_text(""), newline));
                continue;
            }

            if !line.is_char_boundary(indent) {
                eprintln!("line {}: error: inconsistent indentation", first_line + i + 1);
            }
            let line = &line[indent..];

            if let Some(caps) = marker_line_re.captures(line) {
                let indent_amount = caps.get(1).map(|m| m.end() as isize).unwrap();
                prod.chunks.push(Chunk::Indent(indent_amount));
                let nt_idx = prod.nts.len();
                prod.chunks.push(Chunk::Nt(nt_idx));
                prod.nts.push(NonterminalRef {
                    id: self.nt_id(&caps[2]),
                    args: Box::new([]),
                });
                prod.chunks.push(Chunk::Indent(-indent_amount));
                prod.chunks.push(Chunk::Text(self.intern_text(""), newline));
            } else {
                self.parse_line(&mut prod, line, newline);
            }
        }
        prod
    }

    fn parse_line(&mut self, prod: &mut Production, line: &str, full_line: bool) {
        let mut prev_end = 0;
        let marker_re = Regex::new(r"<<([a-zA-Z0-9_]+)>>").unwrap();
        for caps in marker_re.captures_iter(line) {
            let m = caps.get(0).unwrap();

            let start = m.start();
            if start > prev_end {
                let s = self.intern_text(&line[prev_end .. start]);
                prod.chunks.push(Chunk::Text(s, false));
            }
            let nt_idx = prod.nts.len();
            prod.chunks.push(Chunk::Nt(nt_idx));
            prod.nts.push(NonterminalRef {
                id: self.nt_id(&caps[1]),
                args: Box::new([]),
            });

            prev_end = m.end();
        }

        // If full_line is set, we need a final `Text` with `newline` set, even if it contains an
        // empty string.
        if prev_end < line.len() || full_line {
            let s = self.intern_text(&line[prev_end ..]);
            prod.chunks.push(Chunk::Text(s, full_line));
        }
    }

    pub fn finish(self) -> Context {
        Context {
            productions: self.prods,
            nonterminals: self.nts,
        }
    }
}


pub fn parse_grammar(lines: &[&str]) -> Context {
    let mut gb = GrammarBuilder::default();

    // Set up the anonymous nonterminal #0, which expands to `<<start>>` via production #0.
    let root_id = 0;
    gb.nts.push(Nonterminal::default());
    let start_id = gb.nt_id("start");
    gb.add_prod(0, Production {
        vars: vec![],
        args: vec![],
        chunks: vec![Chunk::Nt(0)],
        nts: vec![NonterminalRef {
            id: start_id,
            args: Box::new([]),
        }],
    });

    gb.parse_grammar(lines);
    gb.finish()
}

pub fn parse_grammar_str(s: &str) -> Context {
    let lines = s.lines().map(|l| l.trim_end()).collect::<Vec<_>>();
    parse_grammar(&lines)
}

pub fn read_grammar<R: Read>(mut r: R) -> io::Result<Context> {
    let mut s = String::new();
    r.read_to_string(&mut s)?;
    Ok(parse_grammar_str(&s))
}
