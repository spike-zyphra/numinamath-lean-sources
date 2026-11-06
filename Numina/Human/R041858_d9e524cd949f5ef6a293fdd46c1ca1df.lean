import Mathlib

open Real
/-8.63 Let \( f(x) = x + [\sqrt{x}] \). Prove that for any natural number \( m \),
\[
m, \quad f(m), \quad f(f(m)), \quad f(f(f(m))), \cdots
\]

must contain a perfect square.
(44th Putnam Mathematical Competition, 1983)-/
theorem number_theory_163425 {f : ℝ → ℝ} (hf : ∀ x, f x = x + ⌊Real.sqrt x⌋)
    (m : ℕ) :
    ∃ n, ∃ k, n^2 = f^[k] m := by
  --[Proof] (1) If $m$ is a perfect square number, the conclusion is obvious.
  ---2) (2) If $m$ is not a square number, let $$ m=k^{2}+r \text {, } $$
  --where $k$ and $r$ are positive integers and $0&lt;r \leqslant 2 k$. Let $$ \begin{array}{c} A=\left\{m \mid m=k^{2}+r, 0&lt;r \leqslant k\right\}, \ B=\left\{m \mid m=k^{2}+r, k&lt;r \leqslant 2 k\right\} . \end{array} $$
  --For each $m=k^{2}+r$ in the set $B$, it follows that $$ k&lt;r \leqslant 2 k, $$
--. k+2+(r-1) \ & =k^{2}+4 k+4+(r-k-3) \ k^{2}+3 k+1&lt; & k^{2}+3 k+1+r \leqslant k^{2}+4 k+1 . \end{aligned} $$
  -- so $$ \begin{array}{l} {\left[\sqrt{k^{2}+3 k+1+r}\right]=k+1 .} \ \begin{aligned} f(f(f(f(f(m)))) & =(k+1)^{2}+r+k+k+1 \ & =(k+2)^{2}+(r-2) . \end{aligned} \end{array} $$
  -- And so on, as $f$ is compounded, there is $$ r \rightarrow r-1 \rightarrow r-2 \rightarrow \cdots \rightarrow 2 \rightarrow 1 \rightarrow 0 \text {. } $$
  -- So, when $r=0$, the terms in the series $$ m, \quad f(m), \quad f(f(m)), \cdots $$ must contain perfect squares.
  refine ⟨Real.sqrt (f^[0] m), 0, by simp [hf]⟩