// Navelgazer
// Gaurav Manek
//
// script.js glues the linter to the UI.

"use strict";

// Configuration
var TEST_DELAY = 1000;
var SAVE_DELAY = 1000;

// Global variables
var editor;
var saveTimer;
var dependencies = [];
var gutters = [];
var tooltip;


function $(s){
	return document.getElementById(s);
}
// From: http://stackoverflow.com/a/2901298
function numberWithCommas(x) {
    return x.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ",");
}

function start() {
	tooltip = $('tooltip');
	// Setup
	editor = CodeMirror.fromTextArea($('codeArea'), {
    	lineNumbers: true,
    	mode: "navelgazer",
    	theme: "default",
		lineWrapping: true,
		gutters: ["CodeMirror-linenumbers", "linter"],
		smartIndent: false
  	});
  	//editor.on("gutterClick", handleGutterClick);
  	editor.on("change", handleChange);

  	$('runtimeOut').onclick = runLinter;
  	document.onkeyup = handleKeyboardShortcuts;

  	loadDocument();
};

// This function is invoked when someone clicks the top banner
// or hits ctrl+enter. It runs the parser, performs intermediate
// operations, and loads the code on the machine simulator.
function runLinter() {
	var t_start = performance.now();
	try {
		var pos = editor.getCursor();
		var lines = parser.parse(editor.getValue());

		// Lint the lines. The contents of lines is modified in this process.
		var rv = Linter.lint(lines);
		var pp = PrettyPrint(lines);
		editor.setValue(pp.text);
		editor.setCursor(pos);

		setPrintableArea(pp.columns);
		
		setFlags(rv.flags);
		dependencies = rv.dependencies;

		var t_end = performance.now();
		success("Completed in " + Math.round(t_end-t_start) + " ms");
	} catch (err) {
		if (err instanceof Linter.LinterException || err.name && err.name == "SyntaxError") {
			if(err.name && err.name == "SyntaxError") {
				err.location = err.location.start.line - 1;
			}
			error(err.message, err.location);
			return;
		} else {
			throw err;
		}
	}
}

//
// Responding to UI events.
//

function handleChange() {
	clearTimeout(saveTimer);
	saveTimer = setTimeout(saveDocument, SAVE_DELAY);
}

function saveDocument() {
	if(localStorage)
		localStorage.setItem("NavelgazerString", editor.getValue());
}

function loadDocument() {
	if(localStorage) {
		var cs = localStorage.getItem("NavelgazerString");
		if(cs && cs.trim().length > 0) {
			editor.setValue(cs);
		}
	}
}

//
// Keyboard Interaction
//

function handleKeyboardShortcuts(e) {
  if(e.ctrlKey && e.keyCode ==  13) { // "Ctrl+Enter"
  	runLinter();
  } else {
  	return;
  }
  e.preventDefault();
}

//
// Error printing and jumping within the code.
//

function isNumeric(jump) {
	return !isNaN(parseFloat(jump)) && isFinite(jump);
}

var runtimeOutState = null;
function setRuntimeOut(cl, str) {
	$('runtimeOut').innerText = str;
	$('runtimeOut').className = cl;
	runtimeOutState = { str: str, cl: cl }
}
function revertRuntimeOut() {
	if (!runtimeOutState)
		return;
	$('runtimeOut').innerText = runtimeOutState.str;
	$('runtimeOut').className = runtimeOutState.cl;
}

function error(str, jump) {
	if (str && str.length > 0) {
		if(isNumeric(jump)) {
			str += " (Line " + (jump + 1) + ")";
		}

		setRuntimeOut("runtimeError", str);
	}

	editor.setSelection({line: jump, ch: 0}, {line: jump, ch: null});
	editor.focus();
}

function status(str) {
	setRuntimeOut("runtimeReady", str);
}

function success(str) {
	setRuntimeOut("runtimeGood", str);
}


//
// UI Drawing Functions
//


function setFlags(flags) {
	clearFlags();

	// "COMMENT" is ignored
	var flagValsFromNames = (l) => l.map((k) => LINT_FLAG[k]);
	var flagsGood = flagValsFromNames(["GOOD"]);
	var flagsWarning = flagValsFromNames(["UNLINTED", "TF_WARNING"]);
	var flagsError = flagValsFromNames(["INCORRECT", "FORWARD_DEPENDENCY", "SAME_DEPENDENCY", "MISSING_DEPENDENCY", "EXTRA_DEPENDENCY", "UNRECOGNIZED", "TF_ERROR"]);
	var findFlag = (flg, grp) => flg.findIndex(f => grp.indexOf(f.flag) >= 0) >= 0;

	gutters = [null];

	for(var i = 1; i < flags.length; i++) {
		var cl = "";

		if (findFlag(flags[i], flagsError)) {
			cl = "Error";
		} else if (findFlag(flags[i], flagsWarning)) {
			cl = "Warning";
		} else if (findFlag(flags[i], flagsGood)) {
			cl = "Good";
		}
		
		var text = flags[i].filter((k) => k.hasOwnProperty("text") && k.text != "").map((k) => k.text).join("\n");
		gutters.push(setFlagGutter(i, cl, text));
	}
}

function clearFlags() {
	editor.clearGutter("linter");
	dependencies = [];
	gutters = [];
}

function setFlagGutter(line, cl, tooltip) {
	var marker = document.createElement("div");
	marker.innerHTML = cl==""?"":(cl=="Good"?"✓":"●");
	//if(tooltip != "")
	//	marker.setAttribute("tt", tooltip);
	marker.className = "gutterFlag" + (cl==""?"":(" flag" + cl));
	marker.addEventListener("mouseover", () => handleMouseOver(line, cl, tooltip));
	marker.addEventListener("mouseout", () => handleMouseOut());

	editor.setGutterMarker(line - 1, "linter", marker);

	return marker;
}

function handleMouseOver(i, cl, tt) {
	if (dependencies && dependencies.length > i) {
		dependencies[i].forEach((j) => gutters[j].className += " flagDep");
	}
	if (tt && tt != "") {
		$('runtimeOut').innerHTML = "Line " + Print.linenum(i) + ": " + tt;
		$('runtimeOut').className = "runtimeTT" + cl;
	} else {
		revertRuntimeOut();
	}
}

function handleMouseOut() {
	if(gutters) {
		gutters.forEach(function (o) {
			if(o !== null) {
				o.className = o.className.replace(" flagDep", "");	
			}
		});
	}
	revertRuntimeOut();
}

// Printing functions

function setPrintableArea(cols) {
	var pr = $("printRoot");

	// Remove the existing data:
	while (pr.lastChild) {
    	pr.removeChild(pr.lastChild);
	}

	// Now we build a table:
	var tbl = document.createElement("table");
	tbl.border = "0";
	tbl.setAttribute("cellspacing", "0");
	tbl.setAttribute("cellpadding", "0");

	for (var i = 0; i < cols.length; ++i) {
		var c = cols[i];
		if (Array.isArray(c)) {
			var row = document.createElement('tr');
			for (var j = 0; j < c.length; j++) {
				var cell = document.createElement('td');
				cell.appendChild(document.createTextNode(c[j]));
				row.appendChild(cell);
			}
			row.className="logic"
			tbl.appendChild(row);

		} else {
			if(c == "") {
				c = document.createElement("span");
				c.innerHTML = "&nbsp;"
			} else {
				c = document.createTextNode(c);
			}
			var row = document.createElement('tr');
			var cell = document.createElement('td');
			cell.className = "comment";
			cell.appendChild(c);
			cell.setAttribute("colspan", "5");
			row.appendChild(cell);
			tbl.appendChild(row);

		}
	}

	var attr = document.createElement("div");
	attr.className = "printAttr";
	attr.innerHTML = "<a href=\"http://www.gauravmanek.com\"> Navelgazer by Gaurav Manek</a>";

	pr.appendChild(tbl);
	pr.appendChild(attr);
}