import Mathlib

open Finset Real

/- Example 10) Let $x_{1}, x_{2}, \cdots, x_{n}$ all be positive numbers, prove that:

$$

\frac{x_{1}^{2}}{x_{2}}+\frac{x_{2}^{2}}{x_{3}}+\cdots+\frac{x_{n-1}^{2}}{x_{n}}+\frac{x_{n}^{2}}{x_{1}} \geqslant x_{1}+x_{2}+\cdots+x_{n} .

$$
 -/
theorem inequalities_276904 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i ∈ range n, 0 < x i) :
    ∑ i ∈ range n, (x i) ^ 2 / x ((i + 1) % n) ≥ ∑ i ∈ range n, x i := by
  -- we have 0 < x ((i + 1) % n) for all i ∈ range n
  have hx1 {i} (hi : i ∈ range n) : 0 < x ((i + 1) % n) := by
    apply hx
    simp only [mem_range]
    exact Nat.mod_lt (i + 1) hn
  -- show that ∑ i ∈ range n, x ((i + 1) % n) = ∑ i ∈ range n, x i
  have hsum : ∑ i ∈ range n, x ((i + 1) % n) = ∑ i ∈ range n, x i := by
    nth_rw 1 3 [show n = (n - 1) + 1 by omega]
    rw [sum_range_succ, sum_range_succ']
    congrm ?_ + x (?_)
    · apply sum_congr rfl
      simp
      intro i hi
      congr
      apply Nat.mod_eq_of_lt
      omega
    · simp [show n - 1 + 1 = n by omega]
  calc
    -- prove that (x i) ^ 2 / x ((i + 1) % n ≥ (2 * x i - x ((i + 1) % n) for all i ∈ range n
    ∑ i ∈ range n, (x i) ^ 2 / x ((i + 1) % n) ≥ ∑ i ∈ range n, (2 * x i - x ((i + 1) % n)) := by
        apply sum_le_sum
        intro i hi
        field_simp [ne_of_gt (hx1 hi)]
        rw [le_div_iff₀ (hx1 hi), ←sub_nonneg]
        set rhs := x i ^ 2 + _ - _
        -- simplify the expression and get 0 ≤ (x i - x ((i + 1) % n)) ^ 2
        rw [show rhs = (x i - x ((i + 1) % n)) ^ 2 by ring]
        exact sq_nonneg _
    _ = ∑ i ∈ range n, x i := by
        rw [sum_sub_distrib, ←mul_sum, hsum]
        ring