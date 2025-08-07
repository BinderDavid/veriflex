import Veriflex.Grammar
import Veriflex.Lexer

/-!
# Example Lexer

This file contains a small example of a grammar and how the lexer can be invoked.
-/

namespace Veriflex

/--
The type of tokens the lexer emits.
-/
inductive Token where
  | Identifier : String → Token
  | KeywordData : Token
  | IntLiteral : Nat → Token
  | Whitespace : Token
  deriving BEq, Repr

/--
Regular expression for matching against lowercase ASCII characters.
-/
def AscSmall : RE :=
  unions [ RE.Symbol 'a',
           RE.Symbol 'b',
           RE.Symbol 'c',
           RE.Symbol 'd',
           RE.Symbol 'e',
           RE.Symbol 'f',
           RE.Symbol 'g',
           RE.Symbol 'h',
           RE.Symbol 'i',
           RE.Symbol 'j',
           RE.Symbol 'k',
           RE.Symbol 'l',
           RE.Symbol 'm',
           RE.Symbol 'n',
           RE.Symbol 'o',
           RE.Symbol 'p',
           RE.Symbol 'q',
           RE.Symbol 'r',
           RE.Symbol 's',
           RE.Symbol 't',
           RE.Symbol 'u',
           RE.Symbol 'v',
           RE.Symbol 'w',
           RE.Symbol 'x',
           RE.Symbol 'y',
           RE.Symbol 'z']

/--
Regular expression for digits `0-9`.
-/
def Digit : RE :=
  unions [ RE.Symbol '0',
           RE.Symbol '1',
           RE.Symbol '2',
           RE.Symbol '3',
           RE.Symbol '4',
           RE.Symbol '5',
           RE.Symbol '6',
           RE.Symbol '7',
           RE.Symbol '8',
           RE.Symbol '9']

/--
Regular expression for a non-empty sequence of digits.
-/
def Decimal : RE := RE.Plus Digit

/--
Rule for parsing an identifier.
-/
def Identifier : Rule Token :=
  { re := RE.Plus AscSmall
    action := λ s => Token.Identifier s
  }

/--
Rule for parsing the "data" keyword.
-/
def KeywordData : Rule Token :=
  { re := from_string ['d', 'a', 't', 'a']
    action := λ _ => Token.KeywordData
  }

def parse_digit (c : Char) : Nat :=
  match c with
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | '9' => 9
  | _ => 0

def parse_decimal (ls : List Char) : Nat :=
  let ls_inv : List Char        := ls.reverse
  let digits : List Nat         := ls_inv.map parse_digit
  let zipped : List (Nat × Nat) := digits.zipIdx 0
  let comped : List Nat         := zipped.map (λ ⟨o,pos⟩ => o * (10^pos))
  comped.sum

/--
Rule for parsing an integer literal.
-/
def IntLiteral : Rule Token :=
  { re := Decimal
    action := λ s => Token.IntLiteral (parse_decimal s.toList)
  }


def Whitespace : Rule Token :=
  { re := RE.Plus (RE.Property (λ c => c.isWhitespace))
    action := λ _ => Token.Whitespace
  }

/--
Combined grammar.
Note that the order of the rules is important:
`KeywordData` must occur before `Identifier` because both regular
expressions match the string "data", but this string should be lexed as
a keyword, not an identifier.
-/
def grammar : List (Rule Token) :=
  [KeywordData, Identifier, IntLiteral, Whitespace]

def lexer (s : String) : List Token :=
  (lex s.toList grammar).fst

#guard lexer "data" == [Token.KeywordData]
#guard lexer "foo" == [Token.Identifier "foo"]
#guard lexer "123" == [Token.IntLiteral 123]
#guard lexer "  " == [Token.Whitespace]

end Veriflex
