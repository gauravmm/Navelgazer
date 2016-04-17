// Navelgazer
// Gaurav Manek

// truthfunctional.js: Provides truth-functional expression verification.
// based on known rules.

// Requirement that at least one of the from: objects is not a plain letter.
// (Because the outermost structure is used to look up various rules.)
// Quantifiers, Predicates, and Identity are not allowed. The same expression
// should not appear more than once in the from section.
var rules = [
	// Double negation:
	{ from: ["not not a"], to: "a", name:"double-negation elimination" },
	// Conjunctions and Disjunctions
	{ from: ["a and b"], to: "a", name:"conjunction elimination" },
	{ from: ["a", "b"], to: "a and b", name:"conjunction introduction" },
	{ from: ["a", "b"], to: "a or b", name:"disjunction introduction" },
	{ from: ["a", "not a -> b"], to: "a or b", name:"disjunction introduction" },
	// De Morgan's Laws:
	{ from: ["not(a and b)"], to: "not a or not b", name:"De Morgan's law" },
	{ from: ["not(a or b)"], to: "not a and not b", name:"De Morgan's law" },
	// Modus Ponens and Tollens:
	{ from: ["a -> b", "a"], to: "b", name:"modus ponens" },
	{ from: ["a -> b", "not b"], to: "not a", name:"modus tollens" },
	// Decomposition of conditionals:
	{ from: ["a or not b"], to: "a -> b", name:"disjunction to conditional" },
	{ from: ["c or a or not b"], to: "(c -> a) -> b", name:"disjunction to conditional" },
	{ from: ["c or a or not b"], to: "c -> (a -> b)", name:"disjunction to conditional" },
	{ from: ["a -> b"], to: "a or not b", name:"conditional to disjunction" },
	{ from: ["a -> c -> b"], to: "a or c or not b", name:"conditional to disjunction" },
	// Contradiction
	{ from: ["a -> b", "a -> not b"], to: "not a", name:"contradiction" },
];

var MAX_DEPTH = 2; // Maximum number of iterations to process.

// We parse all the rules and store them in cmpTruths.
// cmpTruths[x][y][z] is structured:
//   x = number of params on the LHS
//   y = Type of the outermost argument
//   z = Index of rule number matching such argument.

var TruthFunctional = (function (rules) {
	var tf$inline = [];
	var tf$lookupFrom = [];
	var tf$lookupTo = [];
	var tf$rules = rules;

	// Take two sorted lists and return a list of elements that are common to both.
	function tf$intersection(a, b){
		var i = 0;
		var j = 0;
		var rv = [];
		while(i < a.length && j < b.length) {
			if (a[i] < b[j]) {
				i++;
			} else if (a[i] > b[j]) {
				j++;
			} else {
				rv.push(a[i]);
				i++;
				j++;
			}
		}
		return rv;
	}

	function tf$init() {
		// We create the empty arrays for all target assignments:
		tf$lookupFrom = [[], [], [], [], [], [], [], [], []];
		tf$lookupTo = [[], [], [], [], [], [], [], [], []];

		for (var i = 0; i < tf$rules.length; ++i) {
			var t = tf$rules[i];
			if(t.from.length > 2) {
				console.log("We only support TF that has at most two antecedents.");
				// Mark it as unusable
				tf$rules[i] = null;
				continue;
			}

			// Swap each rule for the parse:
			t.from = t.from.map(k => parser.parse(k, { startRule:"Expression" }));
			t.to = parser.parse(t.to, { startRule:"Expression" });

			var vars = t.from.map(c => listVariables(c)).reduce((p, c) => p.concat(c.free).concat(c.bound), []);
			t.vars = sortAndUnique(vars);

			// Now we figure out the outermost rule:
			// We are assuming that there is an outermost rule, so we can 
			function addRuleToLookup(cmpLookup, d) {
				cmpLookup[d.type].push(i);
			}
			t.from.forEach((d) => addRuleToLookup(tf$lookupFrom, d));
			addRuleToLookup(tf$lookupTo, t.to);
		}
	}

	// a and b are both lists of mappings, and each mapping is valid
	// for some subset of the same formula. The list of output mappings is
	// the list of all mappings that fit at least one mapping in a and b.
	// We take the cross product of a and b, and include in the final list
	// every combination of elements in a and b that does not conflict:
	function tf$mergeMappings(a, b) {
		if(a.length == 0 || b.length == 0)
			return [];

		var mapLength = a[0].length;

		var mappings = [];
		for(var i = 0; i < a.length; ++i) {
			for(var j = 0; j < b.length; ++j) {
				var candidate = [];	
				for(var k = 0; k < mapLength; ++k) {
					if(a[i][k] === null && b[j][k] === null) {
						candidate.push(null);
					} else if(a[i][k] !== null && b[j][k] !== null) {
						if(ExprEqualExact(a[i][k], b[j][k], true)) {
							candidate.push(OuterDoubleNegationElimination(a[i][k]));
						} else {
							break;
						}
					} else {
						candidate.push(a[i][k]===null?b[j][k]:a[i][k]);
					}
				}

				// If this candidate has a letter for each letter, then we do this:
				if (candidate.length == mapLength) {
					mappings.push(candidate);
				}
			}
		}

		return mappings;
	}

	// We find mappings (sentence letters in template) -> (expr in actual)
	function tf$findExpressionMapping(template, actual, tplVars) {
		// A mapping is similar to that defined in metalogic.js.
		// It is a list of expr, where position i is non-null if it contains an
		// expression mapped to tplVars[i]. 
		
		// tpl: Template expression
		// act: Actual expression
		// Returns a list of mappings, containing every possible mapping that can
		// satisfy this fragment of the expression.
		// Does not expand quantifiers.
		function mp(tpl, act) {
			if (tpl.type == Expressions.TYPE_SENTENCE_LETTER) {
				// DOUBLE NEGATION INTRODUCTION
				// We do not introduce double-negations here because we dynamically introduce them when we examine the premises.
				var idx = tplVars.indexOf(tpl.letter);
				if (idx >= 0) {
					var mapping1 = tplVars.map(k => null);
					mapping1[idx] = OuterDoubleNegationElimination(act);

					return [mapping1];
				} else {
					console.log("TF: Unexpected letter in template.")
				}

			} else {
				// Both sides must be the same type:
				// if they are not, there are no mappings that
				// can make them the same.

				if (tpl.type == Expressions.TYPE_NEGATION) {
					if (act.type == Expressions.TYPE_NEGATION) {
						return mp(tpl.expr, act.expr);
					} else {
						//return mp(tpl.expr, act);
						return mp(tpl.expr, Expressions.Negation(act));
					}
				}

				if (tpl.type != act.type)
					return [];

				if (tpl.type == Expressions.TYPE_PREDICATE || tpl.type == Expressions.TYPE_QUANTIFIER || tpl.type == Expressions.TYPE_IDENTITY) {
					console.log("TF: Expression type in template not allowed!");
					return [];
				
				} else if (tpl.type == Expressions.TYPE_JUNCTION) {
					// Same type of junction and the number of arguments.
					if (tpl.conjunction != act.conjunction || tpl.juncts.length != act.juncts.length)
						return [];

					return tf$findAllMappings([tplVars.map(k => null)], tpl.juncts, act.juncts, mp);

				} else if (tpl.type == Expressions.TYPE_CONDITIONAL) {
					return tf$mergeMappings(mp(tpl.lhs, act.lhs), mp(tpl.rhs, act.rhs));

				} else if (tpl.type == Expressions.TYPE_BICONDITIONAL) {
					return tf$mergeMappings(mp(tpl.lhs, act.lhs), mp(tpl.rhs, act.rhs)).concat(tf$mergeMappings(mp(tpl.lhs, act.rhs), mp(tpl.rhs, act.lhs)));

				}
			}
		}
		
		return mp(template, actual, []);
	}

	function tf$findAllMappings(map, templates, expressions, func) {
		// We first begin by constructing a juncts.length x juncts.length
		// matrix of mappings, where the [i][j]th entry is the result of 
		// attempting to find a mapping between tpl[i] and act[j].

		var mat = templates.map(k => expressions.map(l => []));
		for (var l = 0; l < templates.length; ++l) {
			for (var r = 0; r < expressions.length; ++r) {
				mat[l][r] = func(templates[l], expressions[r]);
			}
		}

		// Now that we have calculated mat, we need to find all possible 
		// matchings between elements of the left and the right such that
		// at least one mapping from left to right exists. The mapping must be
		// total (i.e. every template must have an expression), and must be
		// one-one (i.e. each template must point to a different expression.)
		function permutations(cmaps, used, l) {
			if (cmaps.length == 0 || l >= mat.length) {
				return cmaps;
			}

			var rvmaps = [];
			for(var r = 0; r < mat[l].length; ++r) {
				if (!used[r] && mat[l][r].length > 0) {
					used[r] = true;
					var parms = permutations(tf$mergeMappings(cmaps, mat[l][r]), used, l + 1);
					rvmaps = rvmaps.concat(parms);
					used[r] = false;
				}
			}

			return rvmaps;
		}

		return permutations(map, expressions.map(k => false), 0);
	}

	// Returns a list of expressions generated by applying rule to elements of allTruth,
	// as long as at least one element is a newTruth (has index < newTruthLength.
	function tf$applyRule(rule, allTruth, newTruthLength) {
		// A function that generates null mappings: var newMapping = () => rule.vars.map((l) => null);
		var rv = []; 
		var matchedFrom = [];
		for(var i = 0; i < newTruthLength; ++i) {
			var expr = allTruth[i];

			// We try to map the current new truth to any one of the available sources.
			for(var j = 0; j < rule.from.length; ++j) {
				// We attempt to match expr to rule.from[j].
				var map = tf$findExpressionMapping(rule.from[j], expr, rule.vars);
				if (map.length == 0) {
					// If we find no possible mapping, we continue.
					continue;
				}

				// We find all possible mappings from variables to expressions that are consistent with map
				// that involve all rules except rule.from[j] and all elements from the current to the end of the list.
				// (including the current element).
				var mappings = tf$findAllMappings(map, rule.from.slice(0, j).concat(rule.from.slice(j+1)), allTruth.slice(i), (a, b) => tf$findExpressionMapping(a, b, rule.vars));

				if(mappings.length == 0) {
					continue;
				}

				// We use these to figure out what new truths we've discovered this round:
				var addedTruths = mappings.map(m => ExprReplaceVariable(rule.to, rule.vars, m));
				rv = rv.concat(addedTruths);
			}
		}

		return rv;
	}

	// Returns discT with only unique elements and elements
	// that do not appear in knownT
	function tf$deduplicateTruth(knownT, discT) {
		var rv = [];
		for(var i = 0; i < discT.length; ++i) {
			// Search all elements in knownT and all elements in discT until just before i.
			for(var j = 0; j < knownT.length + i; ++j) {
				var cmpExpr = (j < knownT.length)?knownT[j]:discT[j - knownT.length];
				// We keep the double-negations around in case we need them for future expansion.
				if (ExprEqualExact(cmpExpr, discT[i], true)) {
					break;
				}
			}

			if (j == knownT.length + i) {
				rv.push(discT[i]);
			}
		}

		return rv;
	}

	// Returns a list will all expressions in aloe and their negations:
	function tf$introduceDoubleNegations(aloe) {
		var rv = [];
		for (var i = 0; i < aloe.length; ++i) {
			if (aloe[i].type == Expressions.TYPE_NEGATION) {
				rv.push(aloe[i]);
			} else {
				rv.push(aloe[i]);
				rv.push(Expressions.Negation(Expressions.Negation(aloe[i])));
			}
		}
		return rv;
	}

	// TODO: Extra case: Equality
	//       Extra case: Arbitrary substitution of free variables.
	function tf$truthy(fr, to) {
		// Now we find a superset of possible rules this could apply to:
		var numFrom = fr.length;
		if(numFrom == 0)
			return [{ flag: LINT_FLAG.TF_ERROR, text:Print.rule("TF") + " applied without any premises!" }];

		var oldTruth = [];
		// In case the first rule involves expanding an implicit double-negative, we introduce it here:
		var newTruth = fr.slice(); //tf$introduceDoubleNegations(fr);

		// These are all the possible rules that could apply in the final step of evaluation.
		// These are all the rules that could conceivably lead to the target sentence.
		var candidatesTo = sortAndUnique(tf$lookupTo[Expressions.TYPE_SENTENCE_LETTER].concat(tf$lookupTo[to.type]), true);

		// We apply these rules at most MAX_DEPTH times.
		for (var i = 0; i < MAX_DEPTH; ++i) {
			var candidates = tf$lookupFrom[Expressions.TYPE_SENTENCE_LETTER];
			for (var j = 0; j < newTruth.length; ++j) {
				var t = newTruth[j];
				// Now we add the type of rule to the candidate list:
				candidates = candidates.concat(tf$lookupFrom[t.type]);
			}
			candidates = sortAndUnique(candidates, true);
			// If this is the last round, we only consider rules that can lead to the final step:
			if (i == MAX_DEPTH - 1) {
				candidates = tf$intersection(candidates, candidatesTo);
			}

			// Now we have a list of candidates. candidate[i] is an index into tf$rules containing 
			// the possible rules.
			// Now we try applying every rule in the candidate set. For each rule, we need to find
			// some mapping between expressions in (oldTruth + newTruth) and each element in the from
			// section of the rule. This mapping is found in a similar manner to the FindMapping function
			// in metalogic.js.
			// To speed up processing, we require the inclusion of at least one expression from newTruth 
			// each round. This prevents rederiving already-derived expressions.
			var allTruth = newTruth.concat(oldTruth);
			var newTruthIndex = newTruth.length;
			var discoveredTruth = []; // expressions we know to be true.
			for (var j = 0; j < candidates.length; ++j) {
				var rule = tf$rules[candidates[j]];
				discoveredTruth = discoveredTruth.concat(tf$applyRule(rule, allTruth, newTruthIndex));
				// appliedRules is a list of all discoverable truths as a result of applying this rule.
			}

			// If we didn't discover anything this round, we can't proceed. We stop.
			if(discoveredTruth.length == 0) {
				return [{ flag: LINT_FLAG.TF_WARNING, text:Print.rule("TF") + " exhausted the search space without confirming this deduction." }];
			}

			// Now we check to see if we have reached the target expression:
			for (var j = 0; j < discoveredTruth.length; ++j) {
				if(ExprEqualExact(discoveredTruth[j], to, true)) {
					return [{ flag: LINT_FLAG.GOOD, text:Print.rule("TF") + " solver confirms this is correct." }];
				}
			}

			// We shift newTruths to oldTruths and discoveredTruth to newTruths
			// We deduplicate discoveredTruth in the process.
			oldTruth = oldTruth.concat(newTruth);
			newTruth = tf$deduplicateTruth(oldTruth, discoveredTruth);
		}

		return [{ flag: LINT_FLAG.TF_WARNING, text:Print.rule("TF") + " reached the depth limit without confirming this deduction." }];
	}

	tf$init(rules);
	return {
		checkAndFlag: tf$truthy
	};
})(rules);

// TODO:
// 3) Use these two to aggressively prune discoveredTruth
// 4) Create a double-negative elimination function to remove only the outermost even-numbered negation.
// 5) Use it on both (to) and (discoveredTruth) before pruning, so as to make pruning more effective.