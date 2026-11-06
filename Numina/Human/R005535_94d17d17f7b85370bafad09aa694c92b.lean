import Mathlib

open Real Finset

/-Compute

$$
\sum_{n=1}^{98} \frac{2}{\sqrt{n}+\sqrt{n+2}}+\frac{1}{\sqrt{n+1}+\sqrt{n+2}}
$$-/

theorem algebra_608716 : ∑ n ∈ range 98, (2 / (√((n : ℝ) + 1) + √(n + 3)) + 1 / (√(n + 2) + √(n + 3))) =
3*√11 - 2 * √2 + 19 := by
-- Rewrite the fractions to telescoping forms and split the summation to three parts
  have aux1 : ∀ m : ℕ, 2 / (√((m : ℝ) + 1) + √(m + 3)) = √(m + 3) - √(m + 2) + (√(m + 2) - √(m + 1)) := by
    intro m; rw [sub_add_sub_cancel, div_eq_iff]; nth_rw 3 [add_comm]
    rw [mul_comm, ← sq_sub_sq, sq_sqrt, sq_sqrt]; ring; all_goals positivity
  have aux2 : ∀ m : ℕ, 1 / (√((m : ℝ) + 2) + √(m + 3)) = (√(m + 3) - √(m + 2)) := by
    intro m; rw [div_eq_iff]; nth_rw 3 [add_comm]
    rw [mul_comm, ← sq_sub_sq, sq_sqrt, sq_sqrt]; ring; all_goals positivity
  simp_rw [aux1, aux2]; repeat rw [sum_add_distrib]
-- Define two auxillary functions $f$ and $g$ and apply sum_range_sub to them
  let f : ℕ → ℝ := fun x => √(x + 1); let g : ℕ → ℝ := fun x => √(x + 2)
  have fsum := sum_range_sub f 98; have gsum := sum_range_sub g 98
  dsimp [f, g] at fsum gsum; push_cast at fsum gsum
  simp_rw [add_assoc] at fsum gsum; norm_num1 at fsum gsum
-- Compute the three sums by fsum and gsum, then simplify
  rw [fsum, gsum, show √100 = 10 by rw [sqrt_eq_iff_eq_sq]; all_goals norm_num]
  rw [show √99 = 3*√11 by rw [sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt]; all_goals norm_num]
  simp; ring