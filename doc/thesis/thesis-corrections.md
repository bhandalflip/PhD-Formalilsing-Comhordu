# Thesis corrections

Errors in the [thesis](2014-10-28-phd-thesis.pdf) as written, found while formalising it, and their corrections. Page numbers are the printed ones.

## 1. The listener reads too few fields from a notification

The listener inputs a notification as $\langle r, m'' \rangle$, but the interface forwards it as $\langle r, m, l \rangle$ (rule IFWD-OUT, Table 4.11, p.89), and an input accepts only a message of its own length (PFX-IN-MSG, Table 4.3, p.67). So the listener never accepts a notification. It should input $\langle r, m'', l' \rangle$ and ignore $l'$. The proof of Lemma 6.26 (p.154) already assumes it does, so the results stand.

**Where:** the definition of **listening** (p.122), Example 5.13 (p.124), whose trace label also swaps $m''$ and $r$. **Found in:** [pass-1 report, root cause 4](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#4-listener-notification-arity-also-in-the-thesis).

## 2. Patience needs guarded definitions

Theorem 4.7 says that a process that can't do a $\tau$ action can delay, whatever the definitions. Remark 4.2's own example, $\mathbf{nonsense}(x, y) \overset{\text{def}}{=} \mathbf{nonsense}(x, y)$, can do neither. The theorem holds when every cycle of names calling each other passes through an action prefix. Remark 4.2's stricter rule, a prefix above every name, would be too strong, since **checkRange** calls **listening** under an `if` (p.122). The protocol meets the weaker condition, so its results stand.

**Where:** Theorem 4.7 (p.80), Remark 4.2 (p.69). **Found in:** [#3](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/3).

## 3. Reacting to a threat needs a non-fail-safe mode

These results, about an entity that has been in its current mode $m$ since some time $t$, need the hypothesis $\neg fs(m)$. A fail-safe mode may be its own fail-safe successor (p.44), so an entity in one can react to a threat and come back to **dormant** in the same mode: still $\mathit{currSince}(m, t)$, but no longer tfs and no longer broadcasting. With a zero transition time (p.107) this can all happen within an instant. The safety proof applies these results only to non-fail-safe modes (step 1 of the proof of Theorem 6.1, p.141), so its result stands.

**Where:** Theorems 6.2 (p.143), 6.3 (p.144), 6.6 (p.146) and 6.11 (p.148), Lemma 6.29 (p.154), Listings 7.34 and 7.35 (p.175). **Found in:** [#14](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/14), from the pass-1 report's [root cause 11](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#11-gaps-in-the-model-axioms).

## 4. The proof of Theorem 6.6 assumes a positive transition time

The proof keeps $\mathit{tfs}(m, 0)$ across a discrete step because **tfsCurr** can't leave its state until time passes. With a zero transition time (p.107) it can. The step still holds under correction 3's $\neg fs(m)$, since an entity whose current mode is not fail-safe stays in the tfs states across a discrete step (Listing 7.43, p.178).

**Where:** the proof of Theorem 6.6 (p.146). **Found in:** [#14](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/14).

## 5. The listener's threat test takes the wrong mode's margin

Definition 5.5 takes the sender's mode first and draws the safety margin from its period and transition time, as the proof of Theorem 6.1 needs. The listener passes its own mode first, so its margin comes from the receiver's mode, which may be smaller. Theorem 6.2 does the same, and its statement names modes $m_1$ and $m_2$ that it never introduces. Passing the sender's mode first in both corrects them, and the proof of Theorem 6.1 already reads them that way (p.142), so its result stands.

**Where:** Definition 5.5 (p.108), the definitions of **currPincCheck** and **nextPincCheck** (p.122), Theorem 6.2 and its proof (p.143). **Found in:** [#14](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/14).

## 6. Values are computed outside Boolean expressions too

Remark 4.1 says that values are computed only in Boolean expressions, so that typing matters only there. But the protocol also computes them in the arguments it passes to its definitions: the listener computes its distance from a message's sender, and the overlap component computes its timers. Typing has to cover those arguments too, giving each computed value a type that its uses accept, such as a distance for the listener's range. The results stand once it does.

**Where:** Remark 4.1 (p.65), the overlap component (p.115), the listener (p.122). **Found in:** [#15](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/15), from the pass-1 report's [root cause 5](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#5-range-typing-esubtract-vs-bpossinc).

## 7. Software components can bypass the mode state

The software uses each of $chanStable$, $chanCurr$ and $chanNext$ both ways, to read the mode state and to write it, so two software components can synchronise on one of them directly (SYNC-LR and SYNC-RL). The listener can then take the next mode that the overlap component writes in **tfsNext**, before the mode state does. The overlap component is left waiting in **tfsCurr** for a mode change that never comes. That breaks the proof of Lemma 6.17, which assumes that **tfsNext**'s output reached the mode state, and with it Theorem 6.7. Splitting each of these channels into one that the software reads from and one that it writes to leaves only the mode state at the other end, and the results stand.

**Where:** Table 4.3 (p.67), the mode-state rules of Table 4.15 (p.99) and their description (p.96), the overlap component (p.115), the listener (p.122), Theorem 6.7 (p.146), the proof of Lemma 6.17 (p.151). **Found in:** [#15](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/15), from the pass-1 report's [root cause 9](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#9-internal-synchronisation-on-mode-state-channels).
