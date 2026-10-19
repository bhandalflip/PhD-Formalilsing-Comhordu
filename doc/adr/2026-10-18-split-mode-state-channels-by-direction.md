# Split each mode-state channel into a read channel and a write channel

Date: 2026-10-18
Status: 2026-10-18 accepted

## Context

The software talks to the mode state on three channels, for whether it is stable, for the current mode and for the next mode, and it uses each of them both ways: on the next-mode channel, for example, it reads the next mode and also writes one. The software language lets any two parallel processes synchronise on any channel. So any software whose parallel components do complementary things with the mode state, one reading a channel while another writes on it, gains an internal synchronisation it never wanted. At best this forces unnatural designs that work around the language, and more often, probably, it causes bugs. It caused one in the protocol: the listener could take the next mode that the overlap component writes on its way to a fail-safe mode, which breaks the bound on the time it takes to reach one. The thesis has the same flaw.

## Decision

Each mode-state channel becomes two: one the software reads from and one it writes to. The mode state writes on the first and reads from the second, and the protocol uses each in its one direction. The language does not reserve these channels, so a process can still use one in the wrong direction. It then finds no mode state at the other end, and it can still synchronise with another component by mistake, but only through an obvious bug: writing on a read channel, or reading a write channel.

## Consequences

- Software that uses each channel in its own direction, as the protocol does, never synchronises with itself on a mode-state channel. The mode state is then at the other end of every use, and the lemmas that need it there hold.
- The software rules stay as they were, with no channel treated specially.
- Each mode-state channel now carries one kind of value in one direction. The current-mode channel used to carry a mode one way and nothing the other, which was one reason the typed-variables decision typed variables rather than channels.
- Using these channels correctly is the protocol's job, not the language's. A new protocol could misuse them, and its proof would have to show that it does not.
- The thesis itself stays as submitted. A correction to it records the same flaw and this fix.

## Rationale

The language should not enforce how software uses the channels around it. Real systems misuse reserved ports, and a protocol proved safe only because its language forbids misuse carries a false sense of security: software has to be resilient to misuse in its environment, not shielded from it by the language. What was wrong was that using each channel in both directions made correct software hard to write. Every piece of software had to make sure that it never synchronised with itself on a channel that was meant for the mode state. Splitting the channels by direction lifts that burden and keeps the language general.

## Alternatives considered

### Reserve the mode-state channels in the software rules

Add a premise to the two synchronisation rules saying that the channel is not a mode-state channel, so that only the entity rules can use these channels. This keeps the thesis's three channels and fixes the flaw with one premise per rule. But the rules get messy: their premises have to list the reserved channels, and the parallel delay rule needs the same exception. That rule lets time pass only when no two components offer complementary actions, and it checks this for itself rather than by asking the synchronisation rules, so without the exception it would stop time for a synchronisation that they forbid. The language does know about these channels, since the entity rules use them, but lists of exceptions in the software rules suggest that the check does not belong there. It also takes a small part of the protocol's job, keeping its components off these channels, and gives it to the language.

### Give the channels types

Type each channel as the software's, the interface's or the mode state's. A process may still use any channel, but two software components synchronise only on a software channel, and the delay rule looks only at those. Types are less ugly than lists of exceptions, and a general-purpose language could well have them. But the objection to reserving the channels holds here too: the language, not the protocol, would keep the software off the mode state's channels.

### Leave the channels as they are

We don't believe `safety` can be proved this way, because of the unwanted internal synchronisation.

## Implementation notes

- **Names.** `chanMStable`, `chanMCurr` and `chanMNext` in `src/lang/LanguageFoundations.v` are now `chanMStableRead` and `chanMStableWrite`, `chanMCurrRead` and `chanMCurrWrite`, and `chanMNextRead` and `chanMNextWrite`. They take the software's view, like the entity rules RD-STBL, WRITE-STBL, CURR-READ, CURR-WRITE, NEXT-READ and NEXT-WRITE (`stepDeRdStbl` and so on in `src/lang/EntityLanguage.v`). The position and interface channels already went one way each and are unchanged.
- **Directions.** The mode state outputs on the read channels (`stepMsOutCurrSing`, `stepMsOutCurrTrans`, `stepMsOutNext` and `stepMsOutStable` in `src/lang/ModeStateLanguage.v`) and inputs on the write channels. In the protocol, `dormant`, `init`, `tfsStart`, `rangeBad`, `gotRange`, `currOK` and `currComp` read, and `switchCurr`, `tfsNext`, `tfsCurr` and `ovAbort` write.
- **The rules the alternatives would change.** The synchronisation rules are `stepDpSyncLR` and `stepDpSyncRL`, and the parallel delay rule is `stepTpPar`, all in `src/lang/SoftwareLanguage.v`. `stepTpPar` lets a composition delay only if no action that one side can do within the delay has its complement in the other side's sort, which is why a premise on the first two needs a matching one on it.
- **Lemmas.** `broadcast_read_out_not`, `overlap_read_out_not` and `listener_read_out_not` say no component writes on a read channel, and `broadcast_write_in_not` and `listener_write_in_not` that neither the broadcaster nor the listener reads a write channel, all in `src/protocol/ProtAuxResults.v`. `ent_disc_proc_write` in `src/lang/EntityLanguage.v` says that a write on a write channel inside an entity step is the mode state's input. `overlap_read_out_not` replaces `overlap_mCurr_out_not`.
- **Statements.** `currOK_track_ent` loses the case where the listener read the next mode from the overlap component. `tfsBc_failSafe` and `tfsListen_failSafe_net`, in the cone of `safety`, were false before the split: after the listener took its next mode, the overlap component could wait in `tfsCurr` and then switch to whatever mode a later request named, which need not be fail-safe. They are now proved from `tfs_failSafe_ent` in `src/protocol/EntAuxResults.v`, and `switch_states_mState`, also in the cone, is proved too.
- **Thesis.** Correction 7 in [`thesis-corrections.md`](../thesis/thesis-corrections.md). The thesis's channels are $chanStable$, $chanCurr$ and $chanNext$, with SYNC-LR and SYNC-RL in Table 4.3 (p.67), PAR-DEL in Table 4.5 (p.75) and the entity rules in Table 4.15 (p.99).
- **Report.** [Root cause 9](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#9-internal-synchronisation-on-mode-state-channels) of the first proving pass, whose suggested fix is the first alternative above.
