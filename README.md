# One extra worker rules out the square-root welfare compromise

Can a clearinghouse give both sides average partner ranks on the square-root scale, or average utilities near half the log of market size? With one extra worker, even a clearinghouse that sees everyone's preferences faces two limits. With probability tending to one, the matched workers' average rank is worse than the square-root benchmark and their average utility falls below the half-log benchmark in every stable assignment.

## Market and stability

There are $n\ge 2$ firms and $n+1$ workers. Each firm assigns a utility to each worker, and each worker assigns a utility to each firm. All $2n(n+1)$ utilities are independent rate-one exponentials. An assignment matches every firm to a distinct worker, leaving one worker unmatched.

A firm and a worker can block an assignment if the firm would gain strictly more than $\varepsilon_n=\log(n)/(6\sqrt n)$ and the worker is either unmatched or would also gain strictly more than $\varepsilon_n$. An assignment is stable if it has no blocking pair. A stable assignment exists in every such market.

The switching-cost model follows Pittel and Rudov. The two welfare bounds below are proved in the accompanying note. [Pittel and Rudov, *Stable matchings under relaxed random preferences*](https://doi.org/10.1007/s00182-026-01016-x)

## The two theorems

**Worker outcomes in every stable assignment.** Let $\delta=1/400000$. Write $\bar R_W(M)$ for the average rank that matched workers give their assigned firms (rank 1 is best), and $\bar V_W(M)$ for their average assigned utility. Draw the market once. As $n$ grows, the probability tends to one that every stable assignment $M$ satisfies both inequalities

$$
\bar R_W(M)>n^{1/2+\delta},
\qquad
\bar V_W(M)<(1/2-\delta)\log n.
$$

Both averages use the $n$ matched workers. On that same market event, the lowest average rank a clearinghouse can attain across stable assignments exceeds the rank bound, and the highest average utility it can attain falls below the utility bound. Different stable assignments can attain these two optima.

**Best compromise between firms and workers.** For each stable assignment, compute the mean partner rank on each side among matched agents. Let $C_n$ be the minimum, over stable assignments, of the worse (larger) of those two means. For utility, average over all $n$ firms and separately over all $n+1$ workers, assigning zero to the unmatched worker. Divide each mean by $\log n$. Let $H_n$ be the maximum, over stable assignments, of the smaller of these two normalized means. With probability tending to one, both optima satisfy

$$
\frac{\log C_n}{\log n}>\frac12+\delta,
\qquad
H_n<\frac12-\delta.
$$

## Proof and verification

The unmatched worker is willing to join any firm. If a firm values her at $u$, stability requires that its assigned worker give it utility at least $u-\varepsilon_n$. Matched workers can pose further blocking threats at other firms. The proof bounds the probability that any stable assignment escapes the resulting constraints, then uses a bound on the joint payoffs of firms and workers to obtain both worker inequalities. [Three-page proof](PROOF.pdf) · [LaTeX source](PROOF.tex)

Codex helped formalize the result in Lean. [Challenge.lean](Challenge.lean) defines the model and states the two theorems with their proof slots open. [Solution.lean](Solution.lean) supplies both proofs. [comparator.json](comparator.json) selects them for comparison. To build the proofs locally, run `lake build Solution` from the repository root.
