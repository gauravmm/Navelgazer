// Navelgazer
// Gaurav Manek
//
// expr.js prepares the various expression types

// The uid field is used to rapidly identify identical expressions. Since each Expressions object
// is immutable, every time we encounter a pair of identical expressions, we assign both their uids
// to the lower of the two uids. This still requires us to spend O(n^2) time to deduplicate n expressions,
// but it makes it substantially faster.
// The requirement that the lower uid be chosen is so that, if we are trying to deduplicate a novel set w.r.t.
// an existing set we avoid rewriting any of the existing set.
// There is a method with lower big-O complexity that involves indirection, but that's rather complicated and
// I do not expect it to provide a significant speed boost, so I have not implemented it.
var UID_COUNTER = 0;
var Expressions = {
	TYPE_UNKNOWN: 0,
	TYPE_SENTENCE_LETTER: 1,
	TYPE_PREDICATE: 2,
	TYPE_JUNCTION: 3,
	TYPE_CONDITIONAL: 4,
	TYPE_BICONDITIONAL: 5,
	TYPE_NEGATION: 6,
	TYPE_QUANTIFIER: 7,
	TYPE_IDENTITY: 8,
	COUNT_TYPE: 9,

	SentenceLetter: function (l) {
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_SENTENCE_LETTER,
			letter: l,
			toString: () => l
		}
	},

	Predicate: function (pred, lttr) {
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_PREDICATE,
			name: pred,
			args: lttr,
			argnum: lttr.length,
			toString: () => pred + lttr.map(k => k.toString()).join("")
		}
	},

	Junction: function (conj, exprs) {
		// Merge *juncts if they are the same type.
		// i.e. you want to collapse ((A and B) and C) to (A and B and C)
		// so that the metalogic functions work as intended.

		var juncts = [];
		exprs.forEach(function(e) {
			if(e.type == Expressions.TYPE_JUNCTION && e.conjunction == conj) {
				juncts = juncts.concat(e.juncts);
			} else {
				juncts.push(e);
			}

		})

		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_JUNCTION,
			conjunction: conj,
			juncts: juncts,
			toString: () => "(" + juncts.map(k => k.toString()).join(conj?" ∧ ":" ∨ ") + ")"
		}
	},

	Conditional: function (cond, impl) {
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_CONDITIONAL,
			lhs: cond,
			rhs: impl,
			toString: () => "(" + cond.toString() + " → " + impl.toString() + ")"
		}
	},

	Biconditional: function (lhs, rhs) {
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_BICONDITIONAL,
			lhs: lhs,
			rhs: rhs,
			toString: () => "(" + lhs.toString() + " ≡ " + rhs.toString() + ")"
		}
	},

	Negation: function (e) {
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_NEGATION,
			expr: e,
			toString: () => "¬" + e.toString()
		}
	},

	Quantifier: function (binds, expr) {
		var b = binds.shift();
		if(binds.length > 0) {
			expr = Expressions.Quantifier(binds, expr);
		}
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_QUANTIFIER,
			universal: b.universal,
			letter: b.letter,
			expr: expr,
			toString: function() {
				ex = expr.toString();
				// Force-wrap the RHS of the Quantifier if it is a Predicate:
				if(expr.type == Expressions.TYPE_PREDICATE)
					ex = "(" + ex + ")";
				return "(" + (b.universal?"∀":"∃") + b.letter.toString() + ")" + ex;
			} 
		}
	},

	Identity: function (lhs, rhs, isequal) {
		return {
			uid: UID_COUNTER++,
			type: Expressions.TYPE_IDENTITY,
			equal: isequal,
			lhs: lhs,
			rhs: rhs,
			toString: () => lhs.toString() + (isequal?"=":"≠") + rhs.toString()
		}
	}
};

// To pretty-print flags.
var Print = {
	letter: k => "<span class=\"pp letter\">" + k + "</span>",
	letters: k => k.map(Print.letter).join(", "),
	linenum: k => "<span class=\"pp linenum\">(" + k + ")</span>",
	premise: k => "<span class=\"pp premisenum\">[" + k + "]</span>",
	mapping: (j, k) => "<span class=\"pp mapping\">" + k.map((l,i) => Print.letter(j[i]) + " → " + Print.letter(l)).join(", ") + "</span>",
	rule: k => "<span class=\"pp rule\">" + k + "</span>"
} 
