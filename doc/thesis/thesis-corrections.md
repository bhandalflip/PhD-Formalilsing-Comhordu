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
