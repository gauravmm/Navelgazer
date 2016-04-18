// Navelgazer
// Gaurav Manek

// metalogic.js: Provides functions over statements that 
// compute equality, mappings, etc.

"use strict"

// List all the variables in an expression, find conflicts, and generate
// appropriate flags.
function listVariables(expr_in) {
	var freeLetters = [];
	var boundLetters = [];
	var flags = [];

	function lst(expr, scopedBoundLetters) {
		if (expr.type == Expressions.TYPE_SENTENCE_LETTER) {
			// If the letter is not bound in the current scope:
			if (scopedBoundLetters.indexOf(expr.letter) < 0) {
				// Then it must be free.
				if (freeLetters.indexOf(expr.letter) < 0) {
					freeLetters.push(expr.letter);
				}
			}

		} else if (expr.type == Expressions.TYPE_PREDICATE) {
			expr.args.forEach((p) => lst(p, scopedBoundLetters));

		} else if (expr.type == Expressions.TYPE_JUNCTION) {
			expr.juncts.forEach((p) => lst(p, scopedBoundLetters));
			
		} else if (expr.type == Expressions.TYPE_CONDITIONAL || expr.type == Expressions.TYPE_BICONDITIONAL) {
			lst(expr.lhs, scopedBoundLetters);
			lst(expr.rhs, scopedBoundLetters);

		} else if (expr.type == Expressions.TYPE_NEGATION) {
			lst(expr.expr, scopedBoundLetters);

		} else if (expr.type == Expressions.TYPE_QUANTIFIER) {
			// Check that the current letter is not bound in the current scope.
			if (scopedBoundLetters.indexOf(expr.letter.letter) < 0) {
				// Add it to the list of bound letters.
				if (boundLetters.indexOf(expr.letter.letter) < 0) {
					boundLetters.push(expr.letter.letter);
				}
			} else {
				// If this letter is bound in the current scope, then we need to add a flag.
				flags.push({ flag: LINT_FLAG.LETTER_CONFLICT, text: Print.letter(expr.letter) + " is bound more than once." });
			}
			lst(expr.expr, scopedBoundLetters.concat([expr.letter.letter]));

		} else if (expr.type == Expressions.TYPE_IDENTITY) {
			lst(expr.lhs, scopedBoundLetters);
			lst(expr.rhs, scopedBoundLetters);

		}
	}

	lst(expr_in, []);

	freeLetters.sort();
	boundLetters.sort();

	// Now we check for overlap between freeLetters and boundLetters:
	var i = 0;
	var j = 0;
	while (i < freeLetters.length && j < boundLetters.length) {
		if(freeLetters[i] < boundLetters[j]) {
			i++;
		} else if(freeLetters[i] > boundLetters[j]) {
			j++;
		} else {
			// Damn, we found a common variable between freeLetters and boundLetters
			flags.push({ flag: LINT_FLAG.LETTER_CONFLICT, text: Print.letter(freeLetters[i]) + " is being used as both bound and free." });
			i++;
			j++;
		}
	}

	return { flags: flags, free: freeLetters, bound: boundLetters };
}

// Replace a variable, returning an entirely new object.
function ExprReplaceVariable(expr, fr, to) {
	var mapper = (k) => ExprReplaceVariable(k, fr, to);
	if (expr.type == Expressions.TYPE_SENTENCE_LETTER) {
		// If the letter is not bound in the current scope:
		var idx = fr.indexOf(expr.letter);
		if (idx >= 0) {
			return to[idx];
		}
		return expr;

	} else if (expr.type == Expressions.TYPE_PREDICATE) {
		return Expressions.Predicate(expr.name, expr.args.map(mapper));

	} else if (expr.type == Expressions.TYPE_JUNCTION) {
		return Expressions.Junction(expr.conjunction, expr.juncts.map(mapper));
		
	} else if (expr.type == Expressions.TYPE_CONDITIONAL) {
		return Expressions.Conditional(mapper(expr.lhs), mapper(expr.rhs));
	
	} else if (expr.type == Expressions.TYPE_BICONDITIONAL) {
		return Expressions.Biconditional(mapper(expr.lhs), mapper(expr.rhs));

	} else if (expr.type == Expressions.TYPE_NEGATION) {
		return Expressions.Negation(mapper(expr.expr));

	} else if (expr.type == Expressions.TYPE_QUANTIFIER) {
		return Expressions.Quantifier([mapper(expr.letter)], mapper(expr.expr));

	} else if (expr.type == Expressions.TYPE_IDENTITY) {
		return Expressions.Identity(mapper(expr.lhs), mapper(expr.rhs), expr.equal);

	}
}


// Finds a mapping between variables in lhsFreeVars in lhs and rhs.
// Assumes that lhs and rhs follow the same structure.
// Requires each variable in lhsFreeVars to map to a unique variable
// in rhs.
function ExprFindMappingOneOne(lhs, rhs, lhsFreeVars) {
	var flags = [];
	var mappings = ExprFindMapping(lhs, rhs, lhsFreeVars);
	if (mappings.length == 0) {
		flags.push({ flag: LINT_FLAG.INCORRECT, text: "There is no possible source for " + Print.letters(lhsFreeVars) + " that leads to this sentence." });
		return { mappings: [], flags: flags };
	}

	// We need to check if the mappings are
	//  (a) complete: with no variable unaccounted for, and--
	//  (b) unrepeating: with a one-to-one relationship between variables,
	//  (c) free in main premise: meet the requirement that the mapping
	//       source (i.e. (vars in targetExpr) == lhsFreeVars) are free in or absent
	//       from in the cited line. We don't need to check this because, if it
	//       is bound, the earlier variable check will catch it.
	//  (d) free in premises: meet the requirement that the mapping
	//       destination (i.e. vars in sourceExpr) are not free in any
	//       premises.
	//
	// To establish completeness for all possible mappings, we need only check
	// the first mapping: assuming it works correctly, the algorithm will only
	// leave a mapping incomplete/undefined iff it never exists in the targetExpr
	// (which is the bit inside the UG). Therefore, any one mapping is incomplete iff
	// all mappings are incomplete.

	// (a)
	mappings = mappings.filter(m => m.indexOf("") < 0);
	if (mappings.length == 0) {
		flags.push({ flag: LINT_FLAG.INCORRECT, text: "There are no possible assignments that account for all of " + Print.letters(lhsFreeVars) + "." });
		return { mappings: [], flags: flags };
	}

	// (b)
	mappings = mappings.filter(function(m) {
		var v = m.slice(0);
		v.sort();
		for(var j = 1; j < v.length; ++j) {
			if (v[j - 1] == v[j]) {
				return false;
			}
		}
		return true;
	});
	if (mappings.length == 0) {
		flags.push({ flag: LINT_FLAG.INCORRECT, text: "There are no possible assignments that account for all of " + Print.letters(lhsFreeVars) + " without splitting a sentence letter." });
		return { mappings: [], flags: flags };
	}
	return { mappings: mappings, flags: flags };
}

// Finds a mapping between variables in lhsFreeVars in lhs and rhs.
// Assumes that lhs and rhs follow the same structure.
function ExprFindMapping(lhs, rhs, lhsFreeVars) {
	// getBoundVar, given a list of {lhs:'a', rhs:'a'} objects
	// and a variable, finds it on the lhs, and returns the
	// rhs if available.
	function getBoundVar(boundVars, lhs) {
		for (var i = 0; i < boundVars.length; i++)
			if(boundVars[i].lhs == lhs)
				return boundVars[i].rhs;
		return lhs;
	}
	function isBoundVar(boundVars, lhs) {
		for (var i = 0; i < boundVars.length; i++)
			if(boundVars[i].lhs == lhs)
				return true;
		return false;
	}

	function sortAndUniqueMappings(s) {
		// In order, examine the elements of two mappings and returns a
		// value the first time they differ. If they are similar, then we
		// return 0. 
		function compare(a, b) {
			for (var i = 0; i < lhsFreeVars.length; ++i) {
				if(a[i] < b[i]) {
					return -1;
				} else if (a[i] > b[i]) {
					return 1;
				}
			}
			return 0;
		}

		if (s.length <= 1) {
			return s;
		}

		s.sort(compare);
		var q = s.slice(1).reduce((p, c) => (compare(p[p.length-1], c)==0?p:p.concat([c])), [s[0]]);
		return q;
	}

	// A mapping is a list of strings, where a string at
	// position i is non-empty if it contains the rhs mapping for
	// lhsFreeVars[i]. 
	// a and b are both lists of mappings, and each mapping is valid
	// for some subset of the same formula. The list of output mappings is
	// the list of all mappings that fit at least one mapping in a and b.
	// 
	// We take the cross product of a and b, and include in the final list
	// every combination of a and b that does not conflict:
	function mergeMappings(a, b) {
		if(a.length == 0 || b.length == 0)
			return [];

		var mappings = [];
		for(var i = 0; i < a.length; ++i) {	
			for(var j = 0; j < b.length; ++j) {
				var candidate = [];	
				for(var k = 0; k < lhsFreeVars.length; ++k) {
					if(a[i][k] == "" && b[j][k] == "") {
						candidate.push("");
					} else if(a[i][k] != "" && b[j][k] != "") {
						if(a[i][k] == b[j][k]) {
							candidate.push(a[i][k]);
						} else {
							break;
						}
					} else {
						candidate.push(a[i][k]==""?b[j][k]:a[i][k]);
					}
				}

				// If this candidate has a letter for each letter, then we
				// do this:
				if (candidate.length == lhsFreeVars.length) {
					mappings.push(candidate);
				}
			}
		}

		var rv = sortAndUniqueMappings(mappings);
		return rv;
	}

	// lhs: Left-hand side structur
	// rhs: Right-hand side structure
	// boundVars: A list of {lhs:'a', rhs:'a'} objects mapping
	// bound variables from the lhs to the rhs.
	// We return a list of mappings, containing every possible mapping that can
	// satisfy this fragment of the expression.
	function mp(lhs, rhs, boundVars) {
		// Both sides must be the same type:
		// if they are not, there are no mappings that
		// can make them the same.
		if (lhs.type != rhs.type)
			return [];

		var identityMap = [lhsFreeVars.map(k => "")];
		if (lhs.type == Expressions.TYPE_SENTENCE_LETTER) {
			// If this mapping is bound variable, then it can't be
			// a free variable, and lhsFreeVars only includes free
			// variables. 
			var mapping = lhsFreeVars.map(k => "");
			if (isBoundVar(boundVars, lhs.letter)) {
				return [mapping];
			}
			// If there is a letter in lhsFreeVars that matches lhs.letter
			// then we include rhs in the corresponding position
			var idx = lhsFreeVars.indexOf(lhs.letter);
			if (idx >= 0) {
				mapping[idx] = rhs.letter;
			}
			return [mapping];
		} else if (lhs.type == Expressions.TYPE_PREDICATE) {
			if (lhs.name != rhs.name || lhs.argnum != rhs.argnum)
				return [];

			var mapping = identityMap;

			// Make sure all the the arguments are the same:
			for(var i = 0; i < lhs.args.length; ++i){
				var innermapping = mp(lhs.args[i], rhs.args[i], boundVars);
				mapping = mergeMappings(innermapping, mapping);
				// If there are no valid mappings, then return now.
				if (mapping.length == 0)
					break;
			}
			return mapping;
		} else if (lhs.type == Expressions.TYPE_JUNCTION) {
			// Same type of junction and the number of arguments.
			if (lhs.conjunction != rhs.conjunction || lhs.juncts.length != rhs.juncts.length)
				return [];

			// We have to return every mapping that satisfies this fragment.
			// This is non-trivial.
			// We first begin by constructing a juncts.length x juncts.length
			// matrix of mappings, where the [i][j]th entry is the result of 
			// attempting to find a mapping between lhs[i] and rhs[j].

			var mat = lhs.juncts.map(k => rhs.juncts.map(l => []));
			for (var l = 0; l < lhs.juncts.length; ++l) {
				for (var r = 0; r < rhs.juncts.length; ++r) {
					mat[l][r] = mp(lhs.juncts[l], rhs.juncts[r], boundVars);
				}
			}

			// Now that we have calculated mat, we need to find all possible 
			// matchings between elements of the left and the right such that
			// at least one mapping exists.

			// permutation([], dim) will return every possible permutation
			// of numbers 1..dim
			function permutations(cmaps, used, l) {
				if (cmaps.length == 0 || l >= mat.length) {
					return cmaps;
				}

				var rvmaps = [];
				for(var r = 0; r < mat[l].length; ++r) {
					if (!used[r] && mat[l][r].length > 0) {
						used[r] = true;
						var parms = permutations(mergeMappings(cmaps, mat[l][r]), used, l + 1);
						rvmaps = rvmaps.concat(parms);
						used[r] = false;
					}
				}

				return rvmaps;
			}

			return permutations(identityMap, lhs.juncts.map(k => false), 0);

		} else if (lhs.type == Expressions.TYPE_CONDITIONAL) {
			var rv = mergeMappings(mp(lhs.lhs, rhs.lhs, boundVars), mp(lhs.rhs, rhs.rhs, boundVars));
			return rv;

		} else if (lhs.type == Expressions.TYPE_BICONDITIONAL) {
			return mergeMappings(mp(lhs.lhs, rhs.lhs, boundVars), mp(lhs.rhs, rhs.rhs, boundVars)).concat(mergeMappings(mp(lhs.lhs, rhs.rhs, boundVars), mp(lhs.rhs, rhs.lhs, boundVars)));

		} else if (lhs.type == Expressions.TYPE_NEGATION) {
			return mp(lhs.expr, rhs.expr, boundVars);

		} else if (lhs.type == Expressions.TYPE_QUANTIFIER) {
			// First, we check for the type of quantifier.
			if(lhs.universal != rhs.universal)
				return [];
			// Are the variables already bound?
			if(boundVars.findIndex((k) => (k.lhs == lhs.letter) || (k.rhs == rhs.letter)) >= 0) {
				return [];
			}
			return mp(lhs.expr, rhs.expr, boundVars.concat([{lhs: lhs.letter, rhs: rhs.letter}]));

		} else if (lhs.type == Expressions.TYPE_IDENTITY) {
			if (lhs.equal != rhs.equal)
				return [];
			return mergeMappings(mp(lhs.lhs, rhs.lhs, boundVars), mp(lhs.rhs, rhs.rhs, boundVars)).concat(mergeMappings(mp(lhs.lhs, rhs.rhs, boundVars), mp(lhs.rhs, rhs.lhs, boundVars)));
		}
	}
	
	var rv = mp(lhs, rhs, []);
	return rv;
}

// Calculates exact equality:
//   Where two statements are equal if and only if
//   they share the same structure and the identities of *free* variables.
//   Bound variables may change within their scope without affecting the 
//   equality of two statements. 
// allowDoubleNegatives: if true, expressions with different double-negatives are
// considered the same.
function ExprEqualExact(lhs, rhs, allowDoubleNegatives=false) {
	// getBoundVar, given a list of {lhs:'a', rhs:'a'} objects
	// and a variable, finds it on the lhs, and returns the
	// rhs if available.
	function getBoundVar(boundVars, lhs) {
		for (var i = 0; i < boundVars.length; i++)
			if(boundVars[i].lhs == lhs)
				return boundVars[i].rhs;
		return lhs;
	}

	function updateUids(isSame) {
		if (isSame) {
			//lhs.uid = Math.min(lhs.uid, rhs.uid);
			//rhs.uid = lhs.uid;
		}
		return isSame;
	}

	// lhs: Left-hand side structure
	// rhs: Right-hand side structure
	// boundVars: A list of {lhs:'a', rhs:'a'} objects mapping
	// bound variables from the lhs to the rhs.
	function eq(lhs, rhs, boundVars) {
		// We use a uid to rapidly check for equality in cases where
		// the object pointer is the same.
		if (lhs.uid == rhs.uid)
			return true;

		// We must conduct this check before we compare types.
		if (allowDoubleNegatives) {
			lhs = OuterDoubleNegationElimination(lhs);
			rhs = OuterDoubleNegationElimination(rhs);
		}

		// Both sides must be the same type:
		if (lhs.type != rhs.type)
			return false;

		if (lhs.type == Expressions.TYPE_SENTENCE_LETTER) {
			return updateUids(rhs.letter == getBoundVar(boundVars, lhs.letter));
		} else if (lhs.type == Expressions.TYPE_PREDICATE) {
			if (lhs.name != rhs.name || lhs.argnum != rhs.argnum)
				return updateUids(false);
			// Make sure all the the arguments are the same:
			for(var i = 0; i < lhs.args.length; ++i)
				if (!eq(lhs.args[i], rhs.args[i], boundVars))
					return updateUids(false);

			return updateUids(true);
		} else if (lhs.type == Expressions.TYPE_JUNCTION) {
			// Same type of junction and the number of arguments.
			if (lhs.conjunction != rhs.conjunction || lhs.juncts.length != rhs.juncts.length)
				return updateUids(false);

			// Return true iff some mapping exists so that the LHS and RHS are equal.
			// Set to true if this r is matched to an item.
			var r_matched = rhs.juncts.map(k => false);
			for (var l = 0; l < lhs.juncts.length; ++l) {
				var r_k;
				for (r_k = 0; r_k < rhs.juncts.length; ++r_k) {
					// This little trick means the common case, where each junct is aligned
					// never requires the inner loop to advance.
					var r = (l + r_k) % rhs.juncts.length;
					if (!r_matched[r]) {
						if(eq(lhs.juncts[l], rhs.juncts[r], boundVars)) {
							r_matched[r] = true;
							break;
						}
					}
				}

				if (r_k	== rhs.juncts.length) {
					// We haven't found a mapping for lhs.juncts[l], so we
					// report failure.
					return updateUids(false);
				} 
			}
			// We've found a mapping for all LHS and RHS lists.
			return updateUids(true);

		} else if (lhs.type == Expressions.TYPE_CONDITIONAL) {
			return updateUids(eq(lhs.lhs, rhs.lhs, boundVars) && eq(lhs.rhs, rhs.rhs, boundVars));

		} else if (lhs.type == Expressions.TYPE_BICONDITIONAL) {
			return updateUids(((eq(lhs.lhs, rhs.lhs, boundVars) && eq(lhs.rhs, rhs.rhs, boundVars)) || (eq(lhs.lhs, rhs.rhs, boundVars) && eq(lhs.rhs, rhs.lhs, boundVars))));

		} else if (lhs.type == Expressions.TYPE_NEGATION) {
			return updateUids(eq(lhs.expr, rhs.expr, boundVars));

		} else if (lhs.type == Expressions.TYPE_QUANTIFIER) {
			// First, we check for the type of quantifier.
			if(lhs.universal != rhs.universal)
				return updateUids(false);
			// Are the variables already bound?
			if(boundVars.findIndex((k) => (k.lhs == lhs.letter) || (k.rhs == rhs.letter)) >= 0) {
				return updateUids(false);
			}
			return updateUids(eq(lhs.expr, rhs.expr, boundVars.concat([{lhs: lhs.letter, rhs: rhs.letter}])));

		} else if (lhs.type == Expressions.TYPE_IDENTITY) {
			if (lhs.equal != rhs.equal)
				return updateUids(false);
			return updateUids((eq(lhs.lhs, rhs.lhs, boundVars) && eq(lhs.rhs, rhs.rhs, boundVars)) || (eq(lhs.lhs, rhs.rhs, boundVars) && eq(lhs.rhs, rhs.lhs, boundVars)));
		}
	}

	return eq(lhs, rhs, []);
}

// expr: the expression to clean up.
// Removes only the outermost sets of double-negatives
function OuterDoubleNegationElimination(expr) {
	if (expr.type == Expressions.TYPE_NEGATION && expr.expr.type == Expressions.TYPE_NEGATION) {
		return OuterDoubleNegationElimination(expr.expr.expr); // Return the innermost expression.
	}
	return expr;
}