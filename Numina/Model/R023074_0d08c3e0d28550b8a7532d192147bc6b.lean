import Mathlib

theorem algebra_319607 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (x1 x2 : ℝ) (hx1 : f x1 = x1) (hx2 : f x2 = x2) (hxp : x1 > 0) (hxs : x2 - x1 > 1) :
    b ^ 2 > 2 * (b + 2 * c) ∧ ∀ t, 0 < t ∧ t < x1 → f t > x1 := by
  have eq1 : x1 ^ 2 + b * x1 + c = x1 := by
    rw [hf x1] at hx1
    linarith
  have eq2 : x2 ^ 2 + b * x2 + c = x2 := by
    rw [hf x2] at hx2
    linarith
  have eq3 : x1 + x2 = 1 - b := by
    have eq4 : x1 ^ 2 + b * x1 + c = x1 := by linarith [eq1]
    have eq5 : x2 ^ 2 + b * x2 + c = x2 := by linarith [eq2]
    have eq6 : (x1 - x2) * (x1 + x2 + b - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq6) with h7 h8
    · -- Case $x1 - x2 = 0$, which would mean $x1 = x2$
      exfalso
      have : x1 = x2 := by linarith
      nlinarith
    · -- Case $x1 + x2 + b - 1 = 0$
      linarith
  have eq8 : x1 * x2 = c := by
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
      by_contra h
      have : x1 = x2 := by linarith
      nlinarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - (1 - b)), sq_nonneg (x1 * x2), sq_nonneg (x2 - x1)]
  constructor
  · -- Prove b ^ 2 > 2 * (b + 2 * c)
    have h2 : (x2 - x1) ^ 2 > 1 := by
      nlinarith
    have eq9 : (x2 - x1) ^ 2 = (x1 + x2)^2 - 4 * (x1 * x2) := by
      nlinarith
    rw [eq9] at h2
    rw [show x1 + x2 = 1 - b by linarith [eq3]] at h2
    rw [show x1 * x2 = c by linarith [eq8]] at h2
    nlinarith
  · -- Prove ∀ t, 0 < t ∧ t < x1 → f t > x1
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    have eq11 : f t - x1 = (t - x1) * (t - (x2 - 1)) := by
      rw [hf]
      nlinarith [eq1, eq2, sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        by_contra h
        have : x1 = x2 := by linarith
        nlinarith
      ), sq_nonneg (x1 - x2), sq_nonneg (t - x1), sq_nonneg (t - (x2 - 1)), hxs]
    have h9 : f t - x1 > 0 := by
      rw [eq11]
      have h10 : t - x1 < 0 := by linarith
      have h11 : t - (x2 - 1) < 0 := by
        nlinarith
      nlinarith
    linarith [h9]