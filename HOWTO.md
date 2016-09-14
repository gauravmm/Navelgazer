# Navelgazer
## Documentation
You've probably been sent here by your [philosophy professor](http://rgheck.frege.org/), and you've been told that this will be useful for your [class on introductory logic](frege.org/phil0540/). This page should help you get started using Navelgazer.

But first, a quick word on browsers: use [Google Chrome](https://www.google.com/chrome/). This website has been tested working in Internet Explorer 9, Mozilla Firefox 45.0, and Google Chrome 53, so you _could_ use any of those, but this is a very JavaScript-heavy page and Google Chrome's engine is the fastest. ([Why?](https://developers.google.com/v8/)) This makes a huge difference: I've seen Google Chrome blaze through the default example in 50ms, leaving Firefox behind in the dust at 850ms.

__DISCLAIMER__: Navelgazer is still experimental software. It may incorrectly tell you that something is correct when it is actually wrong, or wrong when it is actually correct. This will (probably) not be considered a valid excuse for having an incorrect solution on homework. _Caveat emptor_.

### What does Navelgazer do?

It checks your first-order logic for errors. When it finds errors, it tells you what is wrong. That's it.


### How do I use it?

You type in your derivation into the __code editor__, and either click the __status bar__ or hit `Ctrl`+`Enter`. Navelgazer will check that each line obeys all the rules of the deductive system, and therefore is valid. Navelgazer will first check if your derivation is syntactically correct, and if there are any errors numbering lines, etc. If that happens, the status bar will turn red, report an error, and the corresponding line will be selected in the code editor. 

If your code is correctly structured, then Navelgazer will check each line for correctness. It does this by:

 1. spliting each line into its respective parts, 
 2. checking that the rule exists,
 3. checking that all the appropriate lines are cited, and--
 4. verifying that the rule is correctly applied.

After completing the check, the status bar will turn green and display a status message like "Completed in ...ms". Navelgazer will automatically reformat your input, and each line will now have either a ✓, an orange ●, or a red ● next to it:

 - If there is a ✓, that means that Navelgazer has verified that your line cites all necessary premises and that you have applied first-order logic correctly in this one line. Hovering over the tick will highlight every ✓ line that is cited (directly or indirectly) by that line. If you are hovering over the the conclusion and some lines are not highlighted, you can safely delete the lines that are not highlighted.
 - If there is a red ●, that means that Navelgazer found an error with the line. You can hover over the symbol with your mouse, and the status bar will describe the error. You can fix the error there and run the checker again.
 - If there is an orange ●, that means that Navelgazer cannot verify the correctness of that line. This should only happen with lines using `TF`, because it is [not possible to verify the `TF` rule every time](https://en.wikipedia.org/wiki/Entscheidungsproblem). The `TF` checker checks for up to two simple logical operations, so if you keep your transformations simple this should not be a problem. (See the supported transformations [here](https://github.com/gauravmm/Navelgazer/blob/production/truthfunctional.js#L11-L33).)

__Note__ that logic should only be considered valid if _all_ lines are ticked. If some of the `TF` lines are flagged orange ● your derivation might still be valid, but you should check that step carefully.


#### Input
The first time you fire Navelgazer up, you will be presented with some sample code. Feel free to experiment with it to get the hang of the input format. The input is structured into lines, with the structure and format very similar to Goldfarb's notation. (The biggest departure is that `EIE` must be on its own line.)

This is the structure of each line:
```
   [2][3]  (8) (∃z)(Txz ∧ Ayz)                  [4](7) EIE
   └┬───┘  └┬┘ └┬─────────────────────────────┘ └┬────────┘
    │       │  (c) Expression                   (d) Rule  
    │      (b) Line number
   (a) Cited lines
```

 a. __Cited lines__ are the lines that this line assumes.
 b. __Line number__ is the number of the current line. If you move lines around, they will automatically be renumbered, and all references updated.
 c. __Expression__ is the actual logical statement.
 d. __Rule__ is the logical rule you applied to derive this line.


__Note:__ The order of operands in commutative (∧, ∨, ≡, ≠) and the grouping of operands in associative (∧, ∨) operations does not matter. Navelgazer automatically checks all possible combinations.

__Note:__ You can use perform multiple `UI`, `UG`, and `EG` in the same line while citing the rule onle once. The default code has an example of this.

__Note:__ If you want the sample code back, just delete all text in the editor, wait for three seconds, then refresh the page.

##### Symbols

You may have noticed that there are fancy unicode symbols in the expressions. Unicode symbols can't be typed easily, and so you can use [good old American](https://www.reddit.com/r/MURICA/) [ASCII](https://en.wikipedia.org/wiki/ASCII) if you want to. When run, Navelgazer will automatically replace them for you. Here are the ASCII equivalents: (The regular equals sign (`=`) is already on most keyboards, and so is not in this list.)

|Symbol | ASCII              |   | Symbol | ASCII |
|------:|:-------------------|---|-------:|:------|
|`∀` | `for all` or `forall` |   | `∧` | `and`    |
|`∃` | `exists`              |   | `∨` | `or`     |
|`¬` | `not`                 |   | `≡` | `<->`    |
|`→` | `->`                  |   | `≠` | `!=`     |


### Other Features

 - __Automatic line renumbering:__ If you want to insert a line in the middle of your derivation, you don't have to renumber everything by hand. Add a blank line (without comments), run Navelgazer, and the numbers of all the lines after your blank line will be increased. Even better, all citations will also be updated automatically!
 - __Robust checking:__ As you manipulate expressions, you may need to rename free (or bound) variables. Navelgazer's equality checking recognizes the change in variable and accounts for that automatically.
 - __Printing:__ If you print the editor page using your browser, it will automatically format the _last-checked_ version of your code for printing. Use `ctrl`+`p` or select `File`→`Print` from the browser menu.


## Bug Reports

Navelgazer is still experimental software, and there are likely several bugs lurking around. If you come across some unexpected behaviour, here's what you do:

  1. Check that the behaviour is unexpected. (i.e. Is it _really_ broken?)
  2. Construct a minimum working example. Because of the way Navelgazer is written, you should be able to construct a five-line input that causes the unexpected behaviour.
  3. Check if anyone else has raised an issue [on Github](https://github.com/gauravmm/NavelGazer/issues).
  4. If not already done, raise an issue [on Github](https://github.com/gauravmm/NavelGazer/issues), posting your minimum example from above. Make sure you tell me what part of the output is incorrect and what the expected output is. (You may have to sign up for an account.)
  5. Wait. Please don't repeatedly email me (or the course staff). The issue tracker is public and everyone can see your issue. Plus, Github already sends me emails. If I don't tag or comment on the issue after two-three days, then please send me an [email](mailto:gaurav@gauravmanek.com).

# Best of luck!
I hope you enjoy learning about logic, and that you find Navelgazer helpful!
