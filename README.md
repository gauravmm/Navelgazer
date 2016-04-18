# Navelgazer
## First-order Logic Linter
Gaurav Manek, 2016

## Description
Navelgazer is designed to be a simple logic linter that both formats input and checks synax and the application of various rules. The language is similar to the specification in the later chapters in [Deductive Logic](http://www.hackettpublishing.com/deductive-logic), and this is intended to be used to help teach that at introductory logic courses in universities.

## Features

Use `Ctrl+Enter` to lint the logic as entered. This will either fail because of an error that prevents understanding (e.g. incorrect notation, duplicated line number) or succeed. If it fails, the relevant part of the code will be selected, and a message will be displayed in the status bar.

If it succeeds, the margin will be updated with various marks that indicate that this statement is:
  - <span>✓</span> Good: syntactically correct and follows from its premises. 
  - <span color="#B90504">●</span> Warning: this statement is syntactically correct but the semantic correctness could not be verified. (This most commonly happens with `TF`)
  - <span color="#ffae19">●</span> Error: this statement is either syntactically or semantically incorrect.

You can hover over these flags to see a detailed description and (for some errors) the correct output instead. The `TF` checker attempts to find a truth-functional derivation of the target line from the cited lines, but due to computational limitations, is not guaranteed to always find the target.

You can print the last-built source code using `Ctrl+p` or by selecting print from the browser menu. The code is automatically formatted for printing.

## Attribution
This work is released under [The MIT License](./LICENSE). It uses a parser generated by [PEG.js](http://pegjs.org/) for parsing, and [CodeMirror](http://codemirror.net/) with packages for syntax highlighting.

This adapts notation from Warren S. Goldfarb's book [Deductive Logic](http://www.hackettpublishing.com/deductive-logic).

The starting framework of code was taken from [an earlier project of mine](https://github.com/gauravmm/AbacusMachineSim).

## Parser
The Parser is built using PEG.js, using the following command:
```
./node_modules/pegjs/bin/pegjs -e parser --allowed-start-rules Code,Expression language.pegjs parser.js
```

## Open Source

### Issues

Feel free to report bugs and request features by creating a [new issue](https://github.com/gauravmm/NavelGazer/issues) and tagging it appropriately.

If you are reporting a bug with the code, please include a minimum working example. If you are reporting a bug with the design/style, please include a screenshot and your OS, browser, and version. (Note that we only support IE9 or better.)

### Contribution

Please only contribute your own work, and only if you are willing to release it under the license of this work.

Branch management is done via [gitflow](http://nvie.com/posts/a-successful-git-branching-model/). Please fork off `develop` and target all pull requests to the same. Feature branches should be named `feature-name` and hotfixes `hotfix-name`. 
