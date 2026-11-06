import Mathlib

open Finset Real

/- Let ${{a}_{k}}=\frac{{{2}^{k}}}{{{3}^{{{2}^{k}}}}+1}$, where $k$ is a natural number. Let $A={{a}_{0}}+{{a}_{1}}+{{a}_{2}}+\cdots +{{a}_{9}}$ and $B={{a}_{0}}{{a}_{1}}\cdots {{a}_{9}}$. Then $\frac{A}{B}=$ ___          ___. -/
theorem algebra_12276 {a : ℕ → ℝ} (ha : ∀ k, a k = 2 ^ k / (3 ^ (2 ^ k) + 1)) :
    (∑ i ∈ range 10, a i) / (∏ i ∈ range 10, a i) =
    (3 ^ (2 ^ 10) - 1) / 2 ^ 47 - 1 / 2 ^ 36 := by
  norm_num [sum_range_succ, prod_range_succ, ha]