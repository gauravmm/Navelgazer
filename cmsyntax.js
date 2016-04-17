// Navelgazer
// Gaurav Manek

// Syntax highlighting mode for the language.
// Uses CodeMirror's simple mode.

CodeMirror.defineSimpleMode("navelgazer", {
  start: [
    {regex: /(for all|forall|∀|exists|∃|not|¬|and|∧|or|∨|->|→|<->|≡|=|!=|≠)/, token: ""},
    {regex: /(P|D|TF|CQ|UI|UG|EG|EII|EIE)/, token: "string"},
    {regex: /(\[[0-9]+\])/, token: "number"},
    {regex: /(\([0-9]+\))/, token: "atom"},
    {regex: /([a-z])/, token: "variable-2"},
    {regex: /([A-Z])/, token: "keyword"},
    {regex: /(\/\/.*)$/, token: "comment"}
  ],
  meta: {
    dontIndentStates: ["comment"],
    lineComment: "//"
  }
});

CodeMirror.defineMIME("script/x-abacm", "abacusmachine");
