# lang/: the language

The multi-tiered language of the thesis (chapter 4, p.58), built on the [model](../model/README.md). It is generic in its process names and their definitions, which a protocol supplies, as [`protocol/`](../protocol/README.md) does for Comhordú.

| File | What it holds |
|---|---|
| [`LanguageFoundations.v`](LanguageFoundations.v) | The typed variables and the values they range over, expressions and their evaluation, and the other low-level parts the tiers share. |
| [`SoftwareLanguage.v`](SoftwareLanguage.v) | The software tier (§4.1, p.61): a CCS-style language with value passing and time. Also the processes a process reaches by calls, whose names cover every name it reaches by steps and delays, and software that uses some channels only for input and others only for output, as it should its entity's channels, with a syntactic check for it. |
| [`ProcEquiv.v`](ProcEquiv.v) | Bisimulation of software processes. |
| [`InterfaceLanguage.v`](InterfaceLanguage.v) | The interface tier (§4.2, p.81), which models an entity's environment with timed lists. |
| [`ModeStateLanguage.v`](ModeStateLanguage.v) | The mode state tier (§4.3, p.90): an entity's current mode, and the next one while it changes. |
| [`EntityLanguage.v`](EntityLanguage.v) | Entities (§4.4, p.93), each made of a process, a position, an interface and a mode state; a predicate on processes lifted to entities; initial entities for a seed process and the entities reachable from them; and an entity step taken to the components of its software, where software that uses its channels correctly meets only the rest of the entity on them. |
| [`NetworkLanguage.v`](NetworkLanguage.v) | Networks of entities (§4.4.1, p.99), with communication between entities and their movement in space, and the notions a protocol proof needs about one entity of a network: its position, the distance to another, its queues, its mode state, its current and next modes, and a predicate on it lifted to the network. Also the networks initial for a seed process and those reachable from them (Definitions 6.1 and 6.2, p.133), with what reachability says of each entity's software, and a network step taken to the components of an entity's software. |
