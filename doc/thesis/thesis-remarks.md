# Thesis remarks

Notable observations about the [thesis](2014-10-28-phd-thesis.pdf) made while formalising it, which are not errors in it. Each gives the printed page and the definition or remark number where there is one, the observation, a minimal example where one helps, and a link to the PR or report that made it. Errors in the thesis are in [`thesis-corrections.md`](thesis-corrections.md) instead.

## 1. A protocol process on its own can get stuck

**Where:** Remark 4.1 (Typing) on p.65; the domain of the transition time $tt$ on p.92, Definition 5.1 on p.107 and Definition 5.8 (Wait Time) on p.114; and the proofs of chapter 6, which reason about entities.

**Observation:** The semantics is defined only over well-typed processes (Remark 4.1), and the transition time $tt(m, m')$ is a partial function, defined exactly when $m \longrightarrow m'$, so the wait time $tw(m, m')$ is partial too. Inside an entity both conditions are guaranteed: the mode state only ever holds a next mode it can reach, and what a process reads on the mode state's channels and on $chanPos$ is what those components hold. A protocol process on its own, as an open system whose inputs come from an arbitrary environment, has neither guarantee, and it can reach states that no entity reaches.

**Example:** From $\mathbf{dormant}$, read $m'$ on $chanNext$, then a mode $m$ on $chanCurr$ with no transition $m \longrightarrow m'$. The process is now $\mathbf{ovWait}(m', tw(m, m') + period(m'), 0)$ with an undefined timer. It still answers $chanAbort$ and $chanBad$, and it broadcasts once its zero timer fires, but its pause timer never runs out, so it never reaches $\mathbf{switchBc}$.

**Why it matters:** A claim about one component of the protocol, such as which state it must be in after an action, is sound inside an entity but not for the component as an open process. The proofs of chapter 6 respect this by reasoning about entities throughout.

**Made in:** [#8](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/8).

## 2. A fail-safe entity still reacts to threats

The listener reacts to a threat, either a message from an entity close enough to be possibly incompatible or a broadcast of its own that reached too small a range, without checking whether its own mode is fail-safe. Both tests keep a positive safety margin for a fail-safe mode, so an entity already in one still starts a transition to its fail-safe successor, which may be the mode it is in. The reaction is harmless, but it is why the results of [correction 3](thesis-corrections.md#3-reacting-to-a-threat-needs-a-non-fail-safe-mode) need a non-fail-safe mode. The model of Chapter 3 has a fail-safe entity ignore such messages (p.53), and the protocol could do the same.

**Where:** Definitions 5.4 and 5.5 (p.108), the listener (p.122). **Made in:** [#14](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/14).
