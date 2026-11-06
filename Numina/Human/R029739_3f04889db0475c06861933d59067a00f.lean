import Mathlib

/- Soit $x \geqslant 0$ un réel. Montrer que :

$$
1+x^{2}+x^{6}+x^{8} \geqslant 4 x^{4}
$$

et trouver les cas d'égalité. -/
theorem inequalities_607249 (x : ℝ) (hx : 0 ≤ x) : 1 + x^2 + x^6 + x^8 ≥ 4 * x^4 ∧
(1 + x^2 + x^6 + x^8 = 4 * x^4 ↔ x = 1) := by
-- Prove the nonnegativity of the following squares
  have : 0 ≤ (x ^ 4 - 1) ^ 2 := by positivity
  have : 0 ≤ (x ^ 3 - x) ^ 2 := by positivity
  constructor
  -- Rearrange terms and rewrite the goal to a square sum form, then use positivity to finish
  · rw [ge_iff_le, ← sub_nonneg]; calc
      _ ≤ (x ^ 4 - 1) ^ 2 + (x ^ 3 - x) ^ 2 := by positivity
      _ = _ := by ring
-- Rearrange terms and rewrite the goal to a square sum form, then use linarith to find $x=1$ 
  constructor
  · intro h; rw [← sub_eq_zero] at h
    rw [show 1 + x ^ 2 + x ^ 6 + x ^ 8 - 4 * x ^ 4 = (x ^ 4 - 1) ^ 2 + (x ^ 3 - x) ^ 2 by ring] at h
    have : (x ^ 4 - 1) ^ 2 = 0 := by rw [eq_iff_le_not_lt]; constructor; all_goals linarith
    simp at this; simp [sub_eq_zero, pow_eq_one_iff_cases] at this
    cases this; assumption; linarith
  intro; simp_all; norm_num