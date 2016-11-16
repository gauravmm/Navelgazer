/*
 * Logic Linter Grammar
 * Gaurav Manek
 * ==========================
 * Built with PegJS
 * Large amounts of this grammar are borrowed from PegJS
 * https://github.com/pegjs/pegjs/blob/master/src/parser.pegjs
 * 
 */
{
  function mapPos(arr, pos) {
      return arr.map(function(v){ return v[pos] });
  }

  function ruleToString(o) {
    var s = ruleToArgString(o);
    if (s == "") {
      return o.name;
    } else {
      return s + " " + o.name;
    }
  }

  function ruleToArgString(o) {
    var s = "";
    if (o.hasOwnProperty("discharged")) {
      s += "[" + o.discharged + "]";
    }
    if (o.hasOwnProperty("line")) {
      s += "(" + o.line + ")";
    }
    if (o.hasOwnProperty("lines")) {
      s += o.lines.map((l) => "(" + l + ")").join("");
    }
    if (o.hasOwnProperty("variable")) {
      s += o.variable;
    } else {
      s += " ";
    }
    return s;
  }

  function addRuleMeta(r) {
    Object.defineProperty(r, 'toString', { value: () => ruleToString(r) });
    Object.defineProperty(r, 'argStr', { value: () => ruleToArgString(r) });
    return r;
  }
}

Code
  = d:(Line / CommentLine) c:(LineTerminatorSequence (Line / CommentLine))* LineTerminatorSequence? _ {
    var rv = [d].concat(mapPos(c, 1));
    var v = rv.pop();
    if (v.isLine || v.text.trim() != "")
      rv.push(v);
    return rv;
  }

CommentLine
  = ws:_ c:SingleLineComment? { return { isLine: false, text: text() }; }

Line
  = _ deps:(Dependency _)* ln:LineNumber _ expr:Expression _ r:Rule _ {
    deps = deps===undefined?[]:mapPos(deps, 0);
    return {
      isLine: true,
      deps: deps,
      line: ln,
      expr: expr,
      rule: r,
      toString: deps.map((i) => "[" + i + "]").join("") + "\t(" + ln + ")\t" + expr.toString() + "\t" + r.toString()
    }
  }

Dependency "premise number"
  = "[" l:Integer "]" {
    return l;
  }
 
LineNumber "line number"
  = "(" l:Integer ")" {
    return l;
  }
  
Rule "rule"
  = "P" {
    return addRuleMeta({ name: "P" });
  }
  / dep:Dependency _ ln:LineNumber _ "D" {
    return addRuleMeta({ name: "D", line: ln, discharged: dep });
  }
  / lns:(LineNumber _)+ "TF" {
    return addRuleMeta({ name: "TF", lines: mapPos(lns, 0) });
  }
  / ln:LineNumber _ nm:("CQ" / "UI" / "UG" / "EG") {
    return addRuleMeta({ name: nm, line: ln });
  }
  / ln:LineNumber vr:Letter _ "EII" {
    return addRuleMeta({ name: "EII", line: ln, variable: vr });
  }
  / dep:Dependency _ ln:LineNumber _ "EIE" {
    return addRuleMeta({ name: "EIE", line: ln, discharged: dep });
  }

//
// Expression Parsing
// 

ExprGroup
  = ExprQuantifier
  / ExprSimple
  / "(" _ expr:Expression _ ")" { return expr; }

// Expressions without parenthesis:
ExprSimple
  = lhs:Letter _ KeywordEquals _ rhs:Letter {
    return Expressions.Identity(lhs, rhs, true);
  }
  / lhs:Letter _ KeywordNotEquals _ rhs:Letter {
    return Expressions.Identity(lhs, rhs, true);
  }
  / KeywordNot _ e:ExprGroup {
    return Expressions.Negation(e);
  }
  / Predicate
  / Letter

Expression
  = cond:ExprGroup _ KeywordThen _ impl:Expression {
    return Expressions.Conditional(cond, impl);
  }
  / exprF:ExprGroup exprR:(_ KeywordAnd _ ExprGroup) + {
    return Expressions.Junction(true, [exprF].concat(mapPos(exprR, 3)));
  } 
  / exprF:ExprGroup exprR:(_ KeywordOr _ ExprGroup) + {
    return Expressions.Junction(false, [exprF].concat(mapPos(exprR, 3)));
  } 
  / lhs:ExprGroup _ KeywordIff _ rhs:ExprGroup {
    return Expressions.Biconditional(lhs, rhs);
  }
  / ExprGroup


ExprQuantifier
  = binds:("("? _ ExprQuantifierInner _ ")"? _ )+ expr:ExprGroup {
    return Expressions.Quantifier(mapPos(binds, 2), expr);
  }

ExprQuantifierInner
  = isForAll:( KeywordExists / KeywordForAll ) _ lttr: Letter {
    return {universal: isForAll, letter: lttr };
  }

//
// Basic Identifier Types
//

Predicate "predicate"
  = pr:[A-Z] lttr:Letter+ {
    return Expressions.Predicate(pr, lttr);
  }

Letter "sentence letter"
  = letter: [a-z] {
    return Expressions.SentenceLetter(letter);
  }

//
// Keywords
//

KeywordForAll "∀"
  = ("for all" / "forall" / "∀") {
    return true;
  }

KeywordExists "∃"
  = ("exists" / "∃") {
    return false;
  }

KeywordNot "¬"
  = "not"
  / "¬"

KeywordAnd "∧"
  = "and"
  / "∧"

KeywordOr "∨"
  = "or"
  / "∨"

KeywordThen "→"
  = "->"
  / "→"

KeywordIff "≡"
  = "<->"
  / "≡"

KeywordEquals "="
  = "="

KeywordNotEquals "≠"
  = "!="
  / "≠"

// 
// Comment Support
// 

Comment "comment"
  = SingleLineComment

SingleLineComment
  = "//" (!LineTerminator SourceCharacter)* { return text(); }
  
  
//
// Core data types
//

AlphaNumeric
  = (Alpha/Numeric)

Integer "integer"
  = Numeric+ { return parseInt(text(), 10); }

Alpha "letter"
  = [a-zA-Z_]

Numeric "digit"
  = [0-9]

SourceCharacter
  = .

WhiteSpace "whitespace"
  = "\t"
  / "\v"
  / "\f"
  / " "
  / "\u00A0"
  / "\uFEFF"

LineTerminator
  = [\n\r\u2028\u2029]

LineTerminatorSequence "end of line"
  = "\n"
  / "\r\n"
  / "\r"
  / "\u2028"
  / "\u2029"

__
  = (WhiteSpace / LineTerminatorSequence / Comment)* {return "";}

_
  = (WhiteSpace)* {return "";}
