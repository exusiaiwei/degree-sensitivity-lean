# DegreeSensitivity: Sharp Bounds on the Sensitivity of Low-Degree Boolean Functions

A **Lean 4** formalization (packaged for the [Palomar](https://palomar-registry.org/) registry; submissions go via [submit.palomar-registry.org](https://submit.palomar-registry.org/)) establishing exact sensitivity bounds, sharpened low-degree upper bounds, and an asymptotic degree–sensitivity exponent lower bound, motivated by Terence Tao's Optimization Constant [#37a](https://teorth.github.io/optimizationproblems/constants/37a.html).

## Scope & Main Results

For a Boolean function $f : \{0, 1\}^n \to \{0, 1\}$, let $s(f)$ denote its maximum sensitivity and $\deg(f)$ the exact total degree of the unique real multilinear polynomial representing $f$ on $\{0, 1\}^n$. Let $B_d := \max \{ s(f) \mid \deg(f) \le d \}$ (which equals the maximum block sensitivity at degree $\le d$, since collapsing disjoint sensitive blocks does not increase polynomial degree).

This development formalizes **13 headline theorems** in [`Challenge.lean`](Challenge.lean) (all proved without `sorry` or `native_decide` in [`Solution.lean`](Solution.lean), using only standard Lean axioms `[propext, Quot.sound, Classical.choice]`):

| Degree $d$ | Wellens (2022) LP Bound | Prior State | This Formalization (Lean 4) | Method |
|---:|---:|---|---|---|
| $2$ | $3$ | $B_2 = 3$ ($\mathrm{NAE}_3$) | **$B_2 = 3$** (sharp) | Explicit witness + symmetrisation Farkas |
| $3$ | $6$ | $B_3 = 6$ (Kushilevitz) | **$B_3 = 6$** (sharp) | Explicit $(6,3,6)$ witness + symmetrisation Farkas |
| $4$ | $10$ | $B_4 = 9$ (Koshta 2026: 479-leaf MILP) | **$B_4 = 9$** (sharp) | **Zero-search 10-line algebraic proof** ($3 \mid 14$) + $\mathrm{NAE}_3 \circ \mathrm{NAE}_3$ witness |
| $5$ | $15$ | $B_5 \le 15$ | **$13 \le B_5 \le 14$** | 4 Terwilliger LP certs + SOS rigidity + no 5-reg $\triangle,2K_2$-free graph on 14 verts + $(13,5,13)$ witness |
| $6$ | $21$ | $B_6 \le 21$ | **$B_6 \le 20$** | 10 Terwilliger LP/PSD certs + SOS rigidity + no 7-reg $\triangle,2K_2$-free graph on 20 verts |
| $7$ | $29$ | $B_7 \le 29$ | **$B_7 \le 28$** | Single pure-integer Subset-$J$ Terwilliger Farkas certificate |
| $8$ | $38$ | $B_8 \le 38$ | **$B_8 \le 36$** | Single pure-integer Subset-$J$ Terwilliger Farkas certificate |
| $9$ | $47$ | $B_9 \le 47$ | **$B_9 \le 46$** | Single pure-integer Subset-$J$ Terwilliger Farkas certificate |

In addition, `kushilevitz_exponent_lower_bound` formally establishes the asymptotic lower bound
$$\frac{\log 6}{\log 3} \le \mathrm{degSensitivityExponent} := \inf\bigl\{\alpha \in \mathbb{R} \;\big|\; \exists C > 0,\;\forall f,\; \deg(f) \ge 1 \Rightarrow s(f) \le C\deg(f)^\alpha\bigr\}$$
via iterated Boolean function composition and the Chebyshev cubic upper bound $s(f) \le 4 \deg(f)^3$.

> **Distinction from Tao's Finite-Supremum Constant $C_{37}$ & Honest Scope Note:**
> `degSensitivityExponent` is the **asymptotic uniform-big-$O$ infimum**, which is distinct from Tao's finite-supremum constant $C_{37} := \sup_{\deg(f) > 1} \frac{\log s(f)}{\log \deg(f)}$ (a finite-degree extremizer could affect $C_{37}$ without affecting the asymptotic infimum; this formalization does not claim the two constants are equal). The corresponding finite-supremum lower bound $\frac{\log 6}{\log 3} \le C_{37}$ follows directly from `kushilevitz_witness` alone.
> The fixed-degree bounds $B_5 \le 14, \dots, B_9 \le 46$ strictly improve the univariate symmetrisation LP bounds of Wellens (2022) and do **not** change the known bounds $[\log_3 6, 2]$ on either `degSensitivityExponent` or $C_{37}$; in particular, $(n=14, d=5)$ remains open (`13 ≤ B_5 ≤ 14`).

## Proof Overview

1. **Zero-Search Algebraic Proof of $B_4 = 9$ (`DegreeSensitivity/Deg4Sharp.lean`):**
   Univariate symmetrisation forces $f$ to be constant on Hamming layers $1, 2, 5, 8, 10$ with $S_3 = 70$. Applying degree-reducing 2-variable and 4-variable difference polynomials $h_1, h_2$ forces every coordinate to have equal layer-3 degree $D(a) = 21$ and every pair to have equal layer-3 codegree $d(a,b) = K$, yielding $45K = 210 \implies 3 \mid 14$, contradiction.
2. **Second-Moment Terwilliger LP/PSD & Forbidden Subgraphs for $B_5 \le 14$ and $B_6 \le 20$ (`DegreeSensitivity/TerwilligerCore.lean`, `TerwilligerPSD.lean`, `RigidityMoments.lean`, `PrimeRegGraph.lean`, `Deg5WorldRecord.lean`, `Deg6WorldRecord.lean`):**
   Using bivariate pair correlations $h_j(a, b) = \mathbb{E}_{|x|=a+b,\,|y|=j,\,|x\cap y|=a}[f(x)f(y)]$ (and elementary sum-of-squares PSD cuts $\mathbb{E}[(\sum_i w_i \Phi_i)^2] \ge 0$ for $d=6$), pure-integer dual certificates force an exact sum-of-squares rigidity identity showing that every pair $\{a,b\}$ has uniform weight-3 codegree and every quadruple $Q$ has $t(Q) \in \{2, 4\}$. Defining a graph $G$ on $n - 1 = 3p - 1$ vertices ($p = 5$ for $d=5$, $p = 7$ for $d=6$) by $ab \in E(G) \iff f(\{a, b, n\}) = 0$ yields a $p$-regular, triangle-free, induced-$2K_2$-free graph on $3p-1$ vertices, which is impossible by elementary neighborhood counting.
3. **Direct Subset-$J$ Terwilliger Farkas Certificates for $B_7 \le 28$, $B_8 \le 36$, $B_9 \le 46$ (`DegreeSensitivity/Deg7WorldRecord.lean`, `Deg8WorldRecord.lean`, `Deg9WorldRecord.lean`):**
   Single-shot, small-integer Farkas dual certificates over the binomial-basis Terwilliger LP directly yield strict infeasibility margins, checked in Lean's kernel via balanced binary trees (`IntTrieVerifier.lean`) without `native_decide`.
4. **Explicit Witnesses (`DegreeSensitivity/WitnessEngine.lean`, `Witnesses.lean`, `Composition.lean`):**
   Fast Möbius Transform verification of $\mathrm{NAE}_3$ $(3,2,3)$, Kushilevitz $(6,3,6)$, $\mathrm{NAE}_3 \circ \mathrm{NAE}_3$ $(9,4,9)$, and an explicit weighted-degree-5 $(13,5,13)$ witness.

## Repository Map

- `Challenge.lean` — Minimal, human-auditable statement surface (131 lines, 13 theorems).
- `Solution.lean` — Connects each declaration in `Challenge.lean` to its `sorry`-free proof.
- `DegreeSensitivity/` — Full modular Lean 4 development (`module` headers throughout).
- `comparator.json` — Palomar Comparator manifest.
- `formalization.yaml` — Structured metadata following `formalization.yaml` v0.4.
- `scripts/verify-comparator.sh`, `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` — Verification and metadata checks.

## Verification

```bash
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
./scripts/verify-comparator.sh
```

*(On 32 GB machines, running `con-ron` with `--jobs=2` avoids peak multi-threaded stack/heap contention while producing the identical `--verified` verdict.)*
