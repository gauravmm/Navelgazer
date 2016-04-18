// Navelgazer
// Gaurav Manek

// Linter.js: Handles the actual linting.

var LINT_FLAG = {
	GOOD: 0,
	FORWARD_DEPENDENCY: 1,
	SAME_DEPENDENCY: 2,
	MISSING_DEPENDENCY: 3,
	EXTRA_DEPENDENCY: 4,
	UNLINTED: 5,
	INCORRECT: 6,
	COMMENT: 7,
	UNRECOGNIZED: 8,
	LETTER_CONFLICT: 9,
	TF_ERROR: 10,
	TF_WARNING: 11
}

var Linter = (function(){
	"use strict";

	// Both arguments are Array of ((Array of Int) or Int)
	var lntr$flattenArray = (v) => v.reduce((p, c) => Array.isArray(c)?p.concat(c):p.concat([c]), []);

	// Check the expected and actual lists, generating flags.
	function lntr$premiseCheck(expected, actual) {
		expected = sortAndUnique(lntr$flattenArray(expected), true);
		actual = sortAndUnique(lntr$flattenArray(actual), true);
		var missing = [];
		var extra = [];

		var i = 0;
		var j = 0;
		while(i < expected.length && j < actual.length) {
			if(expected[i] < actual[j]) {
				missing.push(expected[i]);
				i++;
			} else if(expected[i] > actual[j]) {
				extra.push(actual[j]);
				j++;
			} else {
				i++;
				j++;
			}
		}
		while(i < expected.length) {
			missing.push(expected[i]);
			i++;
		}
		while(j < actual.length) {
			extra.push(actual[j]);
			j++;
		}

		var genText = (t, v) => t + (v.length>1?" premises ":" premise ") + v.map(Print.premise).join(", ");

		var rv = [];
		if (missing.length > 0) {
			rv.push({ flag: LINT_FLAG.MISSING_DEPENDENCY, text:genText("Missing", missing) });
		} 
		if (extra.length > 0) {
			rv.push({ flag: LINT_FLAG.EXTRA_DEPENDENCY, text:genText("Extra", extra) });
		}

		return rv;
	}

	// Returns true if no variable in vars is free in any line.
	// (if getString, returns a string describing what is free.)
	function lntr$areVariablesNotFree(lines, vars, getString) {
		var notfree = vars.map(k => []); // Contains the 
		var rv = lines.reduce(function(prev, depLine) {
			// Skip this if the current line is not a line.
			if (!depLine.isLine) {
				return prev;
			}

			// We can short circuit evaluation of this line because a previous line
			// was false, unless we need to produce a string. Then we do this line as well.
			if (!getString && !prev)
				return false;

			// Every element of vars in every element of lines must not be free.
			// Note that flagged variables are also free.
			return prev && vars.reduce(function(pr, c, j) {
				if (depLine.vars.free.indexOf(c) < 0) {
					return pr;
				} else {
					if (getString) {
						notfree[j].push(depLine.line);
					}
					return false;
				}
			}, true);
		}, true);

		if(!getString)
			return rv;

		notfree = notfree.map((k, i) => k.length==0?"":(Print.letter(vars[i]) + " is free in " + k.map(Print.linenum)));
		notfree = notfree.filter(k => k != "").join(", ");
		notfree = notfree==""?notfree:(notfree + ".");
		
		return notfree;
	}

	var RuleLinters = {
		"P": function(l, lines, idxFromLineNo) { // Page 183, Deductive Logic
			// If all premises are accounted for, then this line is good.
			return lntr$premiseCheck([l.line], l.deps);
		},
		"D": function(l, lines, idxFromLineNo) { // Page 184, Deductive Logic
			// In D, we remove the discharged premise
			// and make the consequent conditional on it.
			var consequent = lines[idxFromLineNo[l.rule.line]];
			
			// The dependencies should be the same as the consequent,
			// without the discharged dependency. We enforce that here.
			var flags = lntr$premiseCheck(consequent.deps.filter((x) => x != l.rule.discharged), l.deps);

			// The consequent must have the discharged premise as a dependency:
			if (consequent.deps.indexOf(l.rule.discharged) < 0) {
				flags.push({ flag: LINT_FLAG.INCORRECT, text: Print.linenum(l.rule.line) + " must have premise " + Print.premise(l.rule.discharged) + " to invoke D." });
			}

			
			if (flags.length > 0) {
				return flags;
			}

			var antecedent = lines[idxFromLineNo[l.rule.discharged]];
			var expected = Expressions.Conditional(antecedent.expr, consequent.expr);

			if (ExprEqualExact(expected, l.expr)) {
				return [{ flag: LINT_FLAG.GOOD }];
			} else {
				return [{ flag: LINT_FLAG.INCORRECT, text: "Incorrect expression, expected:" + expected.toString() }];
			}
		},
		"TF": function(l, lines, idxFromLineNo) { // Page 188, Deductive Logic
			var cited = l.rule.lines.map(k => lines[idxFromLineNo[k]]);

			// We expect all the premises in all the cited lines.
			var flags = lntr$premiseCheck(sortAndUnique(cited.reduce((p, c) => p.concat(c.deps), []), true), l.deps);
			if (flags.length > 0) {
				return flags;
			}

			// Run this through the TF engine and see if it is able to find a solution.
			return TruthFunctional.checkAndFlag(cited.map(k => k.expr), l.expr);
		},
		"CQ": function(l, lines, idxFromLineNo) { // Page 184, Deductive Logic
			// We check that the inner dependencies are copied correctly.
			var dependency = lines[idxFromLineNo[l.rule.line]];
			var flags = lntr$premiseCheck(dependency.deps, l.deps);
			if (flags.length > 0)
				return flags;

			// Between dependency and l, one must have an outer not and one must have an inner not.
			var outerNot = null;
			var innerNot = null;
			if (l.expr.type == Expressions.TYPE_NEGATION) {
				outerNot = l.expr;
				innerNot = dependency.expr;
			} else {
				outerNot = dependency.expr;
				innerNot = l.expr;
			}

			// We strip out the outerNot's not, after checking that it exists.
			if (outerNot.type == Expressions.TYPE_NEGATION) {
				outerNot = outerNot.expr;
			} else {
				return [{ flag: LINT_FLAG.INCORRECT, text: "Missing outer negation symbol." }];
			}

			// CQ can apply over a variable number of letters. Here we figure out how many times to apply CQ here.
			var inLetters = [];

			while((outerNot.type == Expressions.TYPE_QUANTIFIER) && (innerNot.type == Expressions.TYPE_QUANTIFIER)) {
				// Make sure that the CQ changes the quantifier:
				if(outerNot.universal == innerNot.universal) {
					return [{ flag: LINT_FLAG.INCORRECT, text: Print.rule("CQ") + " must change the type of quantifier." }];
				}

				if(outerNot.letter.letter != innerNot.letter.letter) {
					return [{ flag: LINT_FLAG.INCORRECT, text: Print.rule("CQ") + " must preserve the letters and their order." }];
				}

				// We record the letter and continue:
				inLetters.push(outerNot.letter);
				innerNot = innerNot.expr;
				outerNot = outerNot.expr;
			}

			if(inLetters.length == 0) {
				return [{ flag: LINT_FLAG.INCORRECT, text: Print.rule("CQ") + " needs at least one quantifier on both sides." }];
			}

			// Now we check if there is an inner not:
			if (innerNot.type == Expressions.TYPE_NEGATION) {
				innerNot = innerNot.expr;
			} else if(outerNot.type == Expressions.TYPE_NEGATION) {
				// Having a second not inside the outerNot is permissible,
				// This works in cases like: not(exists x)(not G) -> (forall x)
				outerNot = outerNot.expr;
			} else {
				return [{ flag: LINT_FLAG.INCORRECT, text: "Missing inner negation symbol." }];
			}

			// Now we check the inner expression, making sure it is the same.			
			if(ExprEqualExact(innerNot, outerNot)) {
				return [];
			} else {
				return [{ flag: LINT_FLAG.INCORRECT, text: "The expressions within quantifiers do not match." }];
			}
		},
		"UI": function(l, lines, idxFromLineNo) { // Page 184, Deductive Logic
			// In UI, we check that the inner dependency is copied correctly.
			var dependency = lines[idxFromLineNo[l.rule.line]];

			var flags = lntr$premiseCheck(dependency.deps, l.deps);
			if (flags.length > 0)
				return flags;

			// UI can apply over a variable number of letters. Here we figure out how many 
			// times to apply UI to apply here. 
			var innerExpr = dependency.expr;
			var inLetters = [];

			while(innerExpr.type == Expressions.TYPE_QUANTIFIER && innerExpr.universal == true) {
				// If the target expression is also a forall expression, then we break
				// when its letter and the innerExpr letter are the same.
				if(l.expr.type == Expressions.TYPE_QUANTIFIER && l.expr.universal == true) {
					if (l.expr.letter == innerExpr.letter)
						break;
				}
				// We strip off the outermost forall statement.
				inLetters.push(innerExpr.letter.letter);
				// And recur on the inner expression.
				innerExpr = innerExpr.expr;
			}

			if(inLetters.length == 0) {
				flags.push({ flag: LINT_FLAG.INCORRECT, text: Print.rule("UI") + " can only be applied to a universal quantification." });
				return flags;
			}

			// Check that the inner premise matches in some way:
			var mappings = ExprFindMapping(innerExpr, l.expr, inLetters);
			if (mappings.length == 0) {
				flags.push({ flag: LINT_FLAG.INCORRECT, text: "There is no possible assignment for " + Print.letters(inLetters) + " that leads to this sentence." });
			} else {
				flags.push({ flag: LINT_FLAG.GOOD, text: "Possible assignment: " + Print.mapping(inLetters, mappings[0]) + "." });
			}
			
			return flags;
		},
		"UG": function(l, lines, idxFromLineNo) { // Page 184, Deductive Logic; Extended version on 196.
			// In UG, we check that the inner dependency is copied correctly.
			var dependency = lines[idxFromLineNo[l.rule.line]];

			var flags = lntr$premiseCheck(dependency.deps, l.deps);
			if (flags.length > 0)
				return flags;

			// UI can apply over a variable number of letters. Here we figure out how many 
			// times to apply UI to apply here. 
			var sourceExpr = dependency.expr;
			var targetExpr = l.expr;
			var inLetters = []; // The variables used as a source.

			while(targetExpr.type == Expressions.TYPE_QUANTIFIER && targetExpr.universal == true) {
				// If the sourceExpr expression is also a forall expression, then we break
				// when its letter and the targetExpr letter are the same.
				if(sourceExpr.type == Expressions.TYPE_QUANTIFIER && sourceExpr.universal == true) {
					if (sourceExpr.letter == targetExpr.letter)
						break;
				}
				// We strip off the outermost forall statement.
				inLetters.push(targetExpr.letter.letter);
				// And recur on the inner expression.
				targetExpr = targetExpr.expr;
			}


			if(inLetters.length == 0) {
				return [{ flag: LINT_FLAG.INCORRECT, text: Print.rule("UG") + " requires adding a universal quantification." }];
			}

			// Now sourceExpr and targetExpr should map to the same structure with different
			// variables. The variables in targetExpr that we need to discover a mapping to
			// (i.e. they may be changed from sourceExpr to targetExpr. We know what they are
			// called in targetExpr: inLetters, we need to discover this in sourceExpr.)			
			var rv = ExprFindMappingOneOne(targetExpr, sourceExpr, inLetters);
			if (rv.flags.length > 0) {
				return rv.flags;
			}
			var mappings = rv.mappings;

			// (d)			
			var finalMappings = mappings.filter(function(m, i) {
				// return true if any element of m is not free in any line in l.deps.
				return lntr$areVariablesNotFree(l.deps.map(dep => lines[idxFromLineNo[dep]]), m, false);
			});
			if (finalMappings.length == 0) {
				// We need to slim down the notfree list:
				var notfree = lntr$areVariablesNotFree(l.deps.map(dep => lines[idxFromLineNo[dep]]), mappings[0], true);
				return [{ flag: LINT_FLAG.INCORRECT, text: Print.letters(mappings[0]) + " must not be free in any premise. " + notfree }];
			}

			flags.push({ flag: LINT_FLAG.GOOD, text: "Possible assignment: " + Print.mapping(finalMappings[0], inLetters) + "." });
			
			return flags;
		},
		"EG": function(l, lines, idxFromLineNo) { // Page 188, Deductive Logic
			var cited = lines[idxFromLineNo[l.rule.line]];

			// In EG, we check that the premise numbers of this line are the same as the cited line.
			var flags = lntr$premiseCheck(cited.deps, l.deps);
			if (flags.length > 0)
				return flags;

			var sourceExpr = cited.expr;
			var targetExpr = l.expr;
			var inLetters = []; // The variables used as a source.

			while(targetExpr.type == Expressions.TYPE_QUANTIFIER && targetExpr.universal == false) {
				// If the sourceExpr expression is also a forall expression, then we break
				// when its letter and the targetExpr letter are the same.
				if(sourceExpr.type == Expressions.TYPE_QUANTIFIER && sourceExpr.universal == false) {
					if (sourceExpr.letter == targetExpr.letter)
						break;
				}
				// We strip off the outermost forall statement.
				inLetters.push(targetExpr.letter.letter);
				// And recur on the inner expression.
				targetExpr = targetExpr.expr;
			}

			if(inLetters.length == 0) {
				return [{ flag: LINT_FLAG.INCORRECT, text: Print.rule("EG") + " requires adding an existential quantification." }];
			}

			// Now sourceExpr and targetExpr should map to the same structure with different
			// variables. The variables in targetExpr that we need to discover a mapping to
			// (i.e. they may be changed from sourceExpr to targetExpr. We know what they are
			// called in targetExpr: inLetters, we need to discover this in sourceExpr.)			
			var rv = ExprFindMappingOneOne(targetExpr, sourceExpr, inLetters);
			if (rv.flags.length > 0) {
				return rv.flags;
			}
			var mappings = rv.mappings;

			if(mappings.length == 0) {
				return [{ flag: LINT_FLAG.INCORRECT, text: "There is no possible assignment for " + Print.letters(inLetters) + " that leads to this sentence." }];
			} else {
				return [{ flag: LINT_FLAG.GOOD, text: "Possible assignment: " + Print.mapping(mappings[0], inLetters) + "." }];
			}
		},
		"EII": function(l, lines, idxFromLineNo) { // Page 190, Deductive Logic
			var dependency = lines[idxFromLineNo[l.rule.line]];

			// In EII, we need to check that the premises of the current line are
			// the same as the cited line, but also include the current line.
			var flags = lntr$premiseCheck([l.line].concat(dependency.deps), l.deps);
			if (flags.length > 0)
				return flags;

			var innerExpr = dependency.expr;
			var toLetter = l.rule.variable.letter; // This is the letter in the new expression.

			// We need innerExpr to be an existential quantifier.
			if(innerExpr.type != Expressions.TYPE_QUANTIFIER || innerExpr.universal == true) {
				// If it is not, then we complain about it
				return [{ flag: LINT_FLAG.INCORRECT, text: Print.rule("EII") + " can only be applied to an existential quantification." }];
			}

			var fromLetter = innerExpr.letter.letter; // This is the letter in the first expression.
			var actual = l.expr;

			// Check the free-ness of toLetter, the instantial variable.
			// We check that toLetter is not free in any line from the first line to the cited line, inclusive.
			var varIsFree = lntr$areVariablesNotFree(lines.filter(k => k.isLine && k.line <= dependency.line), [toLetter], true);
			if(varIsFree != "") {
				return [{ flag: LINT_FLAG.INCORRECT, text: toLetter + " must not be free in any line up to and including " + Print.linenum(dependency.line) + ". " + varIsFree }];
			}
			
			// We construct the expected expression, and then check for equality.
			var expected = ExprReplaceVariable(innerExpr.expr, [fromLetter], [Expressions.SentenceLetter(toLetter)]);
			if(ExprEqualExact(expected, actual)) {
				return [];
			} else {
				return [{ flag: LINT_FLAG.INCORRECT, text: "The expression within the quantifier is incorrect. Expected: " + expected.toString() }];
			}
		},
		"EIE": function(l, lines, idxFromLineNo) { // Page 190, Deductive Logic
			var cited = lines[idxFromLineNo[l.rule.line]];

			// In EIE, we check that the discharged premise is an EII line, and retreive the flagged variable
			var discharged = lines[idxFromLineNo[l.rule.discharged]];
			if(discharged.rule.name != "EII") {
				return [{ flag: LINT_FLAG.INCORRECT, text: "The discharged premise " + Print.premise(l.rule.discharged) + ", is not an EII line." }];
			}

			// Now we check that the cited line has the discharged line as a premise
			if(cited.deps.indexOf(discharged.line) < 0) {
				return [{ flag: LINT_FLAG.INCORRECT, text: "The cited line " + Print.linenum(cited.line) + " does not have required premise " + Print.premise(discharged.line) + "." }];
			}

			// In EIE, we need to check that the premises of the current line are
			// the same as the cited line excluding the discharged line
			var flags = lntr$premiseCheck(cited.deps.filter(k => k != discharged.line), l.deps);
			if (flags.length > 0)
				return flags;

			// This is the variable bound in the cited line.
			var flagged_var = discharged.rule.variable.letter;
			// Check the free-ness of flagged_var, the instantial variable.
			// We check that flagged_var is not free in any premise of the current line.
			var varIsFree = lntr$areVariablesNotFree(l.deps.map(k => lines[idxFromLineNo[k]]), [flagged_var], true);
			if(varIsFree != "") {
				return [{ flag: LINT_FLAG.INCORRECT, text: Print.letter(flagged_var) + " must not be free in any premise of this line. " + varIsFree }];
			}

			// Now we check that the two expressions are actually equal.
			var actual = l.expr;
			var expected = cited.expr;

			if(ExprEqualExact(expected, actual)) {
				return [];
			} else {
				return [{ flag: LINT_FLAG.INCORRECT, text: "The expression must be the same as in " + Print.linenum(cited.line) + ". Expected: " + expected.toString() }];
			}
		}
	}

	function LinterException(message, loc) {
		this.message = message;
		this.location = loc;
	}

	// Perform the actual linting, 
	function lntr$lint(lines) {
		// We artificially add in an extra line here to force numbers to begin from 1. This way, linter line numbers
		// agree with the editor's line numbers, not the parser's. In PrettyPrint, we remove this line before printing.
		// We also make changes in script.js to 
		lines.splice(0, 0, { isLine: false, text:""});

		// Prepare flags:
		var flags = lines.map((e) => []);
		var mergeFlags = (fl1, fl2) => fl1.map((f, i) => f.concat(fl2[i]));

		// Basic, group-level 
		var idxFromLineNo = lntr$renum(lines);

		// Calculate the reachability and check for bad dependencies:
		var rv = lntr$reach(lines, idxFromLineNo);
		flags = mergeFlags(flags, rv.flags);
		var dependencies = rv.dependencies;

		// We calculate the free and bound variables in each sentence, capturing the
		// scoping issues inherent in each:
		for(var i = 0; i < lines.length; ++i) {
			var l = lines[i];
			if(!l.isLine)
				continue;

			var vars = listVariables(l.expr);
			if (vars.flags.length > 0) {
				flags[i] = flags[i].concat(vars.flags);
			}
			delete vars.flags;

			// If there is a letter flagged, we add that here as well:
			if (l.rule.hasOwnProperty('letter')) {
				vars.flagged = l.rule.letter;
			}

			// We add this to the individual line.
			l.vars = vars;
		}
		
		// Now we check the application of each rule, if there are no existing flags:
		flags = flags.map((f, i) => f.concat(lntr$ruleapplication(lines[i], lines, idxFromLineNo)));

		return { flags: flags, dependencies: dependencies };
	}

	function lntr$ruleapplication(l, lines, idxFromLineNo) {
		if (!l.isLine)
			return [{ flag: LINT_FLAG.COMMENT }];

		if (RuleLinters.hasOwnProperty(l.rule.name)) {
			var rv = (RuleLinters[l.rule.name])(l, lines, idxFromLineNo);
			if (rv.length == 0)
				rv.push({ flag: LINT_FLAG.GOOD });

			return rv;
		} else {
			return [{ flag: LINT_FLAG.UNRECOGNIZED, text: "The rule " + Print.rule(l.rule.name) + " is not recognized."}]
		}
	}

	function lntr$reach(lines, idxFromLineNo) {
		// From each line, which previous lines can you reach?
		// This is used to check for excess dependencies matching.
		// Insufficient dependencies is enforced separately, in a rule
		// by rule manner.

		var flags = lines.map(e => []);

		// Proximate dependencies are the immediate dependencies of
		// each line.
		var proximate = lines.map(function (l){
			if (l.isLine) {
				var rv = l.deps;
				if (l.rule.hasOwnProperty("lines")) {
					rv = rv.concat(l.rule.lines);
				}
				if (l.rule.hasOwnProperty("line")) {
					rv = rv.concat([l.rule.line]);
				}
				return rv;
			} else {
				return [];
			}
		});

		// Ultimate:
		// We flatten and sort the proximate array so that it
		// contains all the dependencies.
		var ultimate = [];
		for(var i = 0; i < proximate.length; ++i) {
			var pxl = proximate[i];
			var nlist = [];
			for(var j = 0; j < pxl.length; ++j) {
				if (idxFromLineNo[pxl[j]] > i) {
					flags[i].push({flag: LINT_FLAG.FORWARD_DEPENDENCY, text: Print.linenum(i) + " depends on " + Print.linenum(pxl[j]) + ", which cannot occur after it."});
				} else if (pxl[j] == i) {
					// You can depend on your own line.
				} else {
					if(idxFromLineNo[pxl[j]] < i) {
						nlist = nlist.concat(ultimate[idxFromLineNo[pxl[j]]]);
					}
				}
			}
			nlist.push(i);
			nlist = sortAndUnique(nlist, true);
			ultimate.push(nlist);
 		}

 		return { flags: flags, dependencies: ultimate };
	}

	function lntr$renum(lines) {
		var rv = [];
		var nextline = 0;

		var maxLine = lines.reduce((p, e) => e.isLine?Math.max(p, e.line):0, 0);
		var newlineno = Array(Math.max(maxLine + 1, lines.length)).fill(-1);

		// Assign line numbers to each line.
		for (var i = 0; i < lines.length; ++i) {
			var l = lines[i];
			if (l.isLine) {
				// Check the current line number.
				if(l.line < 0 || l.line >= newlineno.length) {
					// Line numbers are duplicated. We throw an exception
					// and report this to the user.
					throw new LinterException("Line number out of range.", i);
				} else if (newlineno[l.line] == -1) {
					newlineno[l.line] = nextline;
				} else {
					// Line numbers are duplicated. We throw an exception
					// and report this to the user.
					throw new LinterException("Duplicate line number.", i);
				}

				nextline++;
			} else {
				// Consider a blank line as an empty logic line, this
				// renumbers lines to help users insert lines.
				if (l.text.trim() == "") {
					nextline++;
				}
			}
		}

		function getnum(j, ln) {
			if (j < 0 || j >= newlineno.length || newlineno[j] == -1)
				throw new LinterException("Referenced line number does not exist.", ln);
			return newlineno[j];
		}

		for (var i = 0; i < lines.length; ++i) {
			var l = lines[i];
			if (l.isLine) {
				l.deps = l.deps.map((v) => getnum(v, i));
				l.deps.sort();
				l.line = getnum(l.line, i);
				["line", "discharged"].forEach(function (property) {
					if(l.rule.hasOwnProperty(property)) {
						l.rule[property] = getnum(l.rule[property], i);
					}
				});
				if(l.rule.hasOwnProperty("lines")) {
					l.rule["lines"] = l.rule["lines"].map((v) => getnum(v, i));
					l.rule["lines"].sort();
				}
				rv.push(i);
			} else if (l.text.trim() == "") {
				rv.push(i);
			}
		}

		return rv;
	}

	return {
		lint: lntr$lint,
		LinterException: LinterException
	}
})();

var PAD_NONE = 0;
var PAD_LEFT = 1;
var PAD_RIGHT = 2;
var PADDING = (x) => x % 4;

var NO_SPACE_AFTER = 4;

function PrettyPrint(lines) {
	widths = [0, 0, 0, 0, 0];
	padding = [PAD_LEFT, PAD_LEFT, PAD_RIGHT, PAD_LEFT + NO_SPACE_AFTER, PAD_NONE + NO_SPACE_AFTER];
	text = [];
	// Calculate the column widths
	// We drop the first line number when rendering because we had to add it in earlier.
	// This is a simple hack to force numbering to begin from 1.
	lines.slice(1).forEach(function(l) {
		if (l.isLine) {
			entry = [l.deps.map(k => "["+k+"]").join(""), "("+l.line+")", l.expr.toString(), l.rule.argStr(), l.rule.name];
			text.push(entry);
			entry.forEach((s,i) => widths[i] = Math.max(s.length, widths[i]));
		} else {
			text.push(l.text);
		}
	});

	spaces = (k) => " ".repeat(k);
	// Now we add padding:
	var rv = text.map(function(l) {
		if (Array.isArray(l)) {
			return padding.map(function(pad, i){
				var m = (pad >= NO_SPACE_AFTER)?"":" ";
				if(PADDING(pad) == PAD_NONE)
					return l[i] + m;
				if (PADDING(pad) == PAD_LEFT) {
					return spaces(widths[i] - l[i].length) + l[i] + m;
				} else {
					return l[i] + spaces(widths[i] - l[i].length) + m;
				}
			}).join("");
		} else {
			return l;
		}
	}).join("\n") + "\n";

	return {text: rv, columns: text};
}