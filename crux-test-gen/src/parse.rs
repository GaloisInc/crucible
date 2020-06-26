use std::cmp;
use std::collections::{HashMap, HashSet};
use std::io::{self, Read};
use std::rc::Rc;
use regex::Regex;
use crate::{Context, Production, Nonterminal, ProductionId, NonterminalId, NonterminalRef, Chunk};
use crate::ty::{Ty, CtorTy, VarId};

#[derive(Default)]
struct GrammarBuilder {
    prods: Vec<Production>,
    nts: Vec<Nonterminal>,

    nts_by_name: HashMap<String, NonterminalId>,
    text_interner: HashSet<Rc<str>>,
}

struct ProductionLhs {
    vars: Vec<Rc<str>>,
    nt: NonterminalRef,
}

#[derive(Default)]
struct ProductionRhs {
    chunks: Vec<Chunk>,
    nts: Vec<NonterminalRef>,
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

    pub fn add_prod(&mut self, lhs: ProductionLhs, rhs: ProductionRhs) {
        let ProductionLhs { vars, nt } = lhs;
        let ProductionRhs { chunks, nts } = rhs;

        let id = self.prods.len();
        self.prods.push(Production {
            vars,
            args: nt.args.into(),
            chunks,
            nts,
        });
        self.nts[nt.id].productions.push(id);
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

    fn build_ty(&mut self, p: ParsedTy, vars: &HashMap<&str, VarId>) -> Ty {
        if let Some(&var) = vars.get(p.ctor) {
            assert!(p.args.len() == 0, "unexpected args for type variable {:?}", p.ctor);
            return Ty::Var(var);
        }

        let ctor = CtorTy {
            ctor: self.intern_text(p.ctor),
            args: p.args.into_iter().map(|p2| self.build_ty(p2, vars)).collect::<Rc<[_]>>(),
        };
        Ty::Ctor(Rc::new(ctor))
    }

    fn parse_production_lhs<'s>(
        &mut self,
        s: &'s str,
    ) -> (ProductionLhs, HashMap<&'s str, VarId>) {
        let parsed = Parser::from_str(s).parse_lhs().unwrap();
        let vars_map = make_vars_table(&parsed.vars);
        let lhs = ProductionLhs {
            vars: parsed.vars.into_iter().map(|s| self.intern_text(s)).collect(),
            nt: NonterminalRef {
                id: self.nt_id(&parsed.nt.name),
                args: parsed.nt.args.into_iter().map(|p| self.build_ty(p, &vars_map)).collect(),
            },
        };
        (lhs, vars_map)
    }

    fn parse_nonterminal_ref(
        &mut self,
        s: &str,
        vars_map: &HashMap<&str, VarId>,
    ) -> NonterminalRef {
        let parsed = Parser::from_str(s).parse_nt().unwrap();
        NonterminalRef {
            id: self.nt_id(&parsed.name),
            args: parsed.args.into_iter().map(|p| self.build_ty(p, &vars_map)).collect(),
        }
    }

    fn parse_grammar(&mut self, lines: &[&str]) {
        struct PendingBlock<'a> {
            lhs: ProductionLhs,
            vars_map: HashMap<&'a str, VarId>,
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
                    let rhs = self.parse_block(
                        block.start_line,
                        &lines[block.start_line .. block.end_line],
                        block.min_indent,
                        &block.vars_map,
                    );
                    self.add_prod(block.lhs, rhs);
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
                let (lhs, vars_map) = self.parse_production_lhs(before);

                if after.len() == 0 {
                    // Start of a multi-line block
                    cur_block = Some(PendingBlock {
                        lhs,
                        vars_map,
                        start_line: i + 1,
                        end_line: i + 1,
                        min_indent: usize::MAX,
                    });
                } else {
                    // Single-line case
                    let mut rhs = ProductionRhs::default();
                    self.parse_line(&mut rhs, after, false, &vars_map);
                    self.add_prod(lhs, rhs);
                }
            } else {
                eprintln!("line {}: error: expected `::=`", i + 1);
                continue;
            }
        }

        if let Some(block) = cur_block {
            let rhs = self.parse_block(
                block.start_line,
                &lines[block.start_line .. block.end_line],
                block.min_indent,
                &block.vars_map,
            );
            self.add_prod(block.lhs, rhs);
        }
    }


    fn parse_block(
        &mut self,
        first_line: usize,
        lines: &[&str],
        indent: usize,
        vars_map: &HashMap<&str, VarId>,
    ) -> ProductionRhs {
        let marker_line_re = Regex::new(
            r"^(\s*)<<([a-zA-Z0-9_]+(\[[a-zA-Z0-9_, \[\]]*\])?)>>$",
        ).unwrap();

        let mut prod = ProductionRhs::default();
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
                prod.nts.push(self.parse_nonterminal_ref(&caps[2], vars_map));
                prod.chunks.push(Chunk::Indent(-indent_amount));
                prod.chunks.push(Chunk::Text(self.intern_text(""), newline));
            } else {
                self.parse_line(&mut prod, line, newline, vars_map);
            }
        }
        prod
    }

    fn parse_line(
        &mut self,
        prod: &mut ProductionRhs,
        line: &str,
        full_line: bool,
        vars_map: &HashMap<&str, VarId>,
    ) {
        let mut prev_end = 0;
        let marker_re = Regex::new(
            r"<<([a-zA-Z0-9_]+(\[[a-zA-Z0-9_, \[\]]*\])?)>>",
        ).unwrap();
        for caps in marker_re.captures_iter(line) {
            let m = caps.get(0).unwrap();

            let start = m.start();
            if start > prev_end {
                let s = self.intern_text(&line[prev_end .. start]);
                prod.chunks.push(Chunk::Text(s, false));
            }
            let nt_idx = prod.nts.len();
            prod.chunks.push(Chunk::Nt(nt_idx));
            prod.nts.push(self.parse_nonterminal_ref(&caps[1], vars_map));

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
    gb.add_prod(
        ProductionLhs {
            vars: vec![],
            nt: NonterminalRef {
                id: 0,
                args: Box::new([]),
            },
        },
        ProductionRhs {
            chunks: vec![Chunk::Nt(0)],
            nts: vec![NonterminalRef {
                id: start_id,
                args: Box::new([]),
            }],
        },
    );

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


#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Token<'s> {
    Open,
    Close,
    Comma,
    Word(&'s str),
}

fn tokenize<'s>(s: &'s str) -> Vec<Token<'s>> {
    let word_re = Regex::new(r"^[a-zA-Z0-9_]+").unwrap();
    let space_re = Regex::new(r"^\s+").unwrap();

    let mut s = s;
    let mut tokens = Vec::new();
    while s.len() > 0 {
        if let Some(word) = word_re.find(s) {
            tokens.push(Token::Word(word.as_str()));
            s = &s[word.end()..];
        } else if let Some(space) = space_re.find(s) {
            s = &s[space.end()..];
        } else {
            match s.chars().next().unwrap() {
                '[' => tokens.push(Token::Open),
                ']' => tokens.push(Token::Close),
                ',' => tokens.push(Token::Comma),
                c => panic!("unexpected character {:?}", c),
            }
            s = &s[1..];
        }
    }
    tokens
}

struct Parser<'s> {
    tokens: Vec<Token<'s>>,
    pos: usize,
}

type PResult<T> = Result<T, ()>;

struct ParsedNt<'s> {
    name: &'s str,
    args: Vec<ParsedTy<'s>>,
}

struct ParsedTy<'s> {
    ctor: &'s str,
    args: Vec<ParsedTy<'s>>,
}

struct ParsedLhs<'s> {
    vars: Vec<&'s str>,
    nt: ParsedNt<'s>,
}

impl<'s> Parser<'s> {
    pub fn new(tokens: Vec<Token<'s>>) -> Parser<'s> {
        Parser {
            tokens,
            pos: 0,
        }
    }

    pub fn from_str(s: &'s str) -> Parser<'s> {
        Self::new(tokenize(s))
    }

    pub fn eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    pub fn peek(&self) -> PResult<Token<'s>> {
        let t = self.tokens.get(self.pos).ok_or(())?.clone();
        Ok(t)
    }

    pub fn take(&mut self) -> PResult<Token<'s>> {
        let t = self.peek()?;
        self.pos += 1;
        Ok(t)
    }

    pub fn take_word(&mut self) -> PResult<&'s str> {
        match self.take()? {
            Token::Word(s) => Ok(s),
            _ => Err(()),
        }
    }

    pub fn eat(&mut self, t: Token) -> bool {
        if self.tokens.get(self.pos) == Some(&t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    pub fn eat_word(&mut self, s: &str) -> bool {
        if self.tokens.get(self.pos) == Some(&Token::Word(s)) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    pub fn expect(&mut self, t: Token) -> PResult<()> {
        if !self.eat(t) {
            Err(())
        } else {
            Ok(())
        }
    }

    pub fn parse_ty_list(&mut self) -> PResult<Vec<ParsedTy<'s>>> {
        let mut tys = Vec::new();
        if self.eat(Token::Open) {
            loop {
                tys.push(self.parse_ty()?);
                if self.eat(Token::Close) {
                    break;
                } else {
                    self.expect(Token::Comma)?;
                }
            }
        }
        Ok(tys)
    }

    pub fn parse_ty(&mut self) -> PResult<ParsedTy<'s>> {
        let ctor = self.take_word()?;
        let args = self.parse_ty_list()?;
        Ok(ParsedTy { ctor, args })
    }

    pub fn parse_nt(&mut self) -> PResult<ParsedNt<'s>> {
        let name = self.take_word()?;
        let args = self.parse_ty_list()?;
        Ok(ParsedNt { name, args })
    }

    pub fn parse_lhs(&mut self) -> PResult<ParsedLhs<'s>> {
        let mut vars = Vec::new();
        if self.eat_word("for") {
            self.expect(Token::Open)?;
            loop {
                vars.push(self.take_word()?);
                if self.eat(Token::Close) {
                    break;
                } else {
                    self.expect(Token::Comma)?;
                }
            }
        }

        let nt = self.parse_nt()?;
        Ok(ParsedLhs { vars, nt })
    }
}

fn make_vars_table<'a>(vars: &[&'a str]) -> HashMap<&'a str, VarId> {
    assert!(vars.len() <= u32::MAX as usize);
    vars.iter().enumerate().map(|(idx, &name)| (name, VarId(idx as u32))).collect()
}
