# One extra worker rules out the square-root welfare compromise

Can a clearinghouse give both sides average partner ranks on the square-root scale, or average utilities near half the log of market size? With one extra worker, even a clearinghouse that sees everyone's preferences faces two limits. With probability tending to one, workers miss both benchmarks in every stable assignment.

## Market and stability

There are $n$ firms and $n+1$ workers. Each firm assigns a utility to each worker, and each worker assigns a utility to each firm. All $2n(n+1)$ utilities are independent rate-one exponentials. An assignment matches every firm to a distinct worker, leaving one worker unmatched.

A firm and a worker can block an assignment if the firm would gain strictly more than $\varepsilon_n=\log(n)/(6\sqrt n)$ and the worker is either unmatched or would also gain strictly more than $\varepsilon_n$. An assignment is stable if it has no blocking pair. A stable assignment exists in every such market.

The switching-cost model follows Pittel and Rudov. The two welfare bounds below are proved in the accompanying note. [Pittel and Rudov, *Stable matchings under relaxed random preferences*](https://doi.org/10.1007/s00182-026-01016-x)

## The two theorems

**Worker outcomes in every stable assignment.** Let $\delta=1/400000$. Write $\bar R_W(M)$ for the average rank that matched workers give their assigned firms (rank 1 is best), and $\bar V_W(M)$ for their average assigned utility. Draw the market once. As $n$ grows, the probability tends to one that every stable assignment $M$ satisfies both inequalities

$$
\bar R_W(M)>n^{1/2+\delta},
\qquad
\bar V_W(M)<(1/2-\delta)\log n.
$$

Both averages use the $n$ matched workers. A clearinghouse can pick the stable assignment that workers like best by either measure, even using a different assignment for each measure. Both bounds still hold in the same market.

**Best compromise between firms and workers.** Let $C_n$ be the smallest, over stable assignments, of the larger of the two sides' average partner ranks. Let $H_n$ be the largest, over stable assignments, of the smaller of the two sides' population-average utilities divided by $\log n$. The rank calculation includes matched agents on each side. The utility calculation includes all workers and assigns zero to the unmatched worker. With probability tending to one,

$$
\frac{\log C_n}{\log n}>\frac12+\delta,
\qquad
H_n<\frac12-\delta.
$$

## Proof and verification

The unmatched worker can approach every firm. To prevent blocking, some firms must take workers who would themselves be willing to move. The proof follows those threats across possible assignments and bounds how much utility is left for workers once firms satisfy the resulting constraints. [Three-page proof](PROOF.pdf) · [LaTeX source](PROOF.tex)

Codex helped formalize the result in Lean. [Challenge.lean](Challenge.lean) defines the model and states the two theorems with their proof slots open. [Solution.lean](Solution.lean) supplies both proofs. [comparator.json](comparator.json) selects them for comparison. To build the proofs locally, run `lake build Solution` from the repository root.
