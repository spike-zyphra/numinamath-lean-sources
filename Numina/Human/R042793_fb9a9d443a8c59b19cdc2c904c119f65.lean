import Mathlib

open Real

/- 1. If the inequality $\sqrt{x}+\sqrt{y} \leqslant k \sqrt{5 x+y}$ holds for any positive real numbers $x, y$, then the minimum value of the real number $k$ is $\qquad$ -/
theorem inequalities_192965  :
    IsLeast {k : ℝ | ∀ x y : ℝ, x > 0 → y > 0 → √x + √y ≤ k * √(5 * x + y)} (√30 / 5) := by
  constructor
  -- first prove √30 / 5 is in the set
  . rintro x y hx hy
    -- define √(1/5), 1 and √(5x), √y as functions to use cauchy schwarze
    let f := fun (i : Fin 2) ↦ match i with
      | 0 => √(1 / 5)
      | 1 => 1
    let g := fun (i : Fin 2) ↦ match i with
      | 0 => √(5 * x)
      | 1 => √y
    --- use cauchy schwarze and simplify
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ) f g
    simp [f, g] at h
    rw [← Real.sqrt_mul (show 0 ≤ 5 by norm_num)] at h
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h
    -- we only need to show √(1/5 + 1) is √30/5
    convert h using 2
    norm_num
    -- simplify to show both equal
    rw [show (30 : ℝ) = 6 * 5 by norm_num, Real.sqrt_mul (by norm_num)]
    have : 0 < √ 5 := by simp
    field_simp
    ring_nf
    simp
  -- prove √30 / 5 is a lower bound
  . rintro k h
    -- plug in values 1, 25
    specialize h 1 25
    simp at h
    norm_num at h
    -- do manipulation to show the inequality proves the bound
    simp [show (25:ℝ) = 5 ^ 2 by norm_num] at h
    replace h := mul_le_mul_of_nonneg_right h (show 0 ≤ √30 by simp)
    ring_nf at h
    simp at h
    linarith