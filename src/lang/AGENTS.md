# src/lang/: rules for the language

- The language files are generic in the process names and their definitions. A protocol plugs them in; see [`../protocol/AGENTS.md`](../protocol/AGENTS.md).
- Put a language file's generic code in one `Section` whose `Context` takes the class instances. Rocq drops a section's notations, tactics and `Open Scope` when it ends, so put `Reserved Notation` above the section and declare each notation again after it.
- Place tactics by where they are used, so that the section never has to close and reopen. Each extra `Section`/`End` pair is clutter.
  - A tactic that needs nothing from the section goes above it.
  - A tactic that needs the section's lemmas or notations goes inside the section if more than one proof there uses it, and after the section if more than one proof in later files uses it. Both is fine, and the two copies may differ, because uses outside the section may need a slightly different tactic.
  - A tactic with only one use isn't worth defining. Write that proof without it.
