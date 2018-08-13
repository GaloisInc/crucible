This project defines a concrete syntax for a certain subset of the
registerized Crucible CFGs.

Some features are intentionally omitted, because they require
compile-time additions to Crucible in the form of type class
instances. In particular, there is no syntax for:

 * Recursive types

 * Extensions

 * Concrete types


How to use


General syntax

The basic syntax is based on a simplified variant of Lisp
S-expressions, without support for dotted pairs or special syntax for
quote or quasiquote. A syntactic form is either an atom or matching
opening and closing parentheses with a whitespace-delimited sequence
of syntactic forms between them.


The atoms are as follows:

 * Identifiers are either keywords or Crucible atom names. Every
   identifier that is not a language keyword is a Crucible atom
   name. Identifiers consist of a letter-like character followed by
   zero or more digits or letter-like characters. Letter-like
   characters are those considered letters by Unicode, or any of the
   characters <, >, =, +, -, *, /, !, _, \, or ?.

   The keywords are documented below, under each special form.

 * Function names consist of an @ character followed by an identifier.

 * Register names consist of a $ character followed by an identifier.

 * Numbers consist of an optional '+' or '-' followed by an unsigned
   number and an optional denominator. Unsigned numbers are either
   decimal literals, octal literals, or hexadecimal literals, using
   the typical syntax with a 0-prefix. A denominator is a '/'
   character followed by an unsigned number.

 * Boolean literals are #t or #T and #f or #F.

 * String literals are delimited by double-quotes, and support
   escaping with \.


Line comments are preceded by ;, and block comments are delimited by
#| and |#.


Functions

A program consists of a sequence of function definitions. A function
definition is a form that begins with the keyword "defun", followed by
a function name, argument list, return type, and body. A function name
is a function name atom. An argument list is a form that contains zero
or more argument specs. An argument spec is a two-element form, where
the first is a Crucible atom name, and the second is a form that
denotes a type. A return type is a form that denotes a type.

A function body consists of an optional list of registers, a start
block, and zero or more further blocks. A list of registers is a form
that begins with the keyword "registers" and is followed by zero or
more register specifications. A register specification is a form
containing an atom name and a type.

Blocks consist of the defblock keyword followed by a block body. Block
bodies are zero or more ordinary statements followed by a terminating
statement. The first block must begin with "start" instead of
"defblock". In the future, the restriction that the start block comes
first may be relaxed.

Types

t ::= 'Any' | 'Unit' | 'Bool' | 'Nat' | 'Real' | 'ComplexReal' | 'Char' | 'String'
    | '(' 'Vector' t ')' | '(' 'BitVector' n ')' | '(' '->' t ... t ')' 


Expressions



Registers


Blocks


Statements




