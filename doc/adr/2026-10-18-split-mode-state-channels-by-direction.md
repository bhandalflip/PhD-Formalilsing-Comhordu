# Split each mode-state channel into a read channel and a write channel

Date: 2026-10-18
Status: 2026-10-18 accepted

## Context

The software talks to the mode state on three channels, for whether it is stable, for the current mode and for the next mode, and it used each of them both ways: on the next-mode channel, for example, it reads the next mode and also writes one. The software language lets any two parallel processes synchronise on any channel, so two components of the protocol could talk to each other on a mode-state channel and leave the mode state out. The listener could take the next mode that the overlap component writes on its way to a fail-safe mode, and the overlap component would then wait for a mode change that never comes. That breaks the bound on the time it takes to reach a fail-safe mode, and two lemmas in the cone of `safety` with it. The thesis has the same flaw.

## Decision

Each mode-state channel becomes two: one the software reads from and one it writes to. The mode state writes on the first and reads from the second, and the protocol uses each in its one direction. The language does not reserve these channels. A process that writes where it should read is still a process of the language; it just finds no mode state at the other end.

## Consequences

- No two components of the protocol can meet on a mode-state channel, since none of them writes where another reads, so the mode state is at the other end of every use and the lemmas that need it there hold.
- The language's rules stay as they were, and none of them names a channel it treats specially.
- Each mode-state channel now carries one kind of value in one direction, which the typed-variables decision found the current-mode channel did not.
- Using these channels correctly is the protocol's job, not the language's. A new protocol could misuse them, and its proof would have to show that it does not.
- The thesis is corrected to match.

## Rationale

The language should not enforce how software uses the channels around it. Real systems misuse reserved ports, and a protocol proved safe only because its language forbids misuse carries a false sense of security: software has to be correct in its environment, not shielded from it. What was wrong was not that misuse was possible, but that one channel served two directions, so that even correct software could be overheard. Splitting the channels by direction fixes that and keeps the language general.

## Alternatives considered

### Reserve the mode-state channels in the software rules

Add a premise to the two synchronisation rules saying that the channel is not a mode-state channel, and the same exception to the maximal-progress check of the parallel delay rule, so that only the entity rules can use these channels. This keeps the thesis's three channels and fixes the flaw with one premise per rule. But the language's rules get messy: their premises have to talk about reserved channels, which a generic language should know nothing about, and the delay rule needs the exception too, or time would stop for a synchronisation that can never happen. It also writes the protocol's convention into the language, so `safety` would be proved in a world where misuse is impossible by decree rather than one where the software avoids it.

### Leave the channels as they are

Change nothing in the language and work around the flaw in the proofs. No hypothesis can rule the synchronisation out, because it happens in reachable states of the protocol. The bound on the time to reach a fail-safe mode stays false, and so do the lemmas of `safety` that rest on the mode state being at the other end.

## Implementation notes

- **Names.** `chanMStable`, `chanMCurr` and `chanMNext` in `src/lang/LanguageFoundations.v` are now `chanMStableRead` and `chanMStableWrite`, `chanMCurrRead` and `chanMCurrWrite`, and `chanMNextRead` and `chanMNextWrite`. They take the software's view, like the entity rules RD-STBL, WRITE-STBL, CURR-READ, CURR-WRITE, NEXT-READ and NEXT-WRITE (`stepDeRdStbl` and so on in `src/lang/EntityLanguage.v`). The position and interface channels already went one way each and are unchanged.
- **Directions.** The mode state outputs on the read channels (`stepMsOutCurrSing`, `stepMsOutCurrTrans`, `stepMsOutNext` and `stepMsOutStable` in `src/lang/ModeStateLanguage.v`) and inputs on the write channels. In the protocol, `dormant`, `init`, `tfsStart`, `rangeBad`, `gotRange`, `currOK` and `currComp` read, and `switchCurr`, `tfsNext`, `tfsCurr` and `ovAbort` write.
- **Lemmas.** `broadcast_read_out_not`, `overlap_read_out_not` and `listener_read_out_not` say no component writes on a read channel, and `broadcast_write_in_not`, `overlap_write_in_not` and `listener_write_in_not` that none reads from a write channel, all in `src/protocol/ProtAuxResults.v`. `ent_disc_proc_write` in `src/lang/EntityLanguage.v` says that a write on `chanMCurrWrite` or `chanMStableWrite` inside an entity step is the mode state's input. `overlap_read_out_not` replaces `overlap_mCurr_out_not`.
- **Statements.** `currOK_track_ent` loses the case where the listener read the next mode from the overlap component. `switch_states_mState`, in the cone of `safety`, is proved.
- **Thesis.** Correction 7 in [`thesis-corrections.md`](../thesis/thesis-corrections.md). The thesis's channels are $chanStable$, $chanCurr$ and $chanNext$, with SYNC-LR and SYNC-RL in Table 4.3 (p.67), PAR-DEL in Table 4.5 (p.75) and the entity rules in Table 4.15 (p.99).
- **Report.** [Root cause 9](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#9-internal-synchronisation-on-mode-state-channels) of the first proving pass, whose suggested fix is the first alternative above.
