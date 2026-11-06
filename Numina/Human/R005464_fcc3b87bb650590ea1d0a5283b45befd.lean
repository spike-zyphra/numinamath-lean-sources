import Mathlib

/-
Find the slopes of all lines passing through
the origin and tangent to the curve $y^{2}=x^{3}+39 x-35$.
-/

theorem calculus_608395 (x y : ℝ) (h : y ^ 2 = x ^ 3 + 39 * x - 35)
  (tan : (3 * x ^ 2 + 39) * x = y * (2 * y)):
  (y / x = √51 / 2 ∨ y / x = -√51 / 2) ∨
  (y / x = √285 / 5 ∨ y / x = -√285 / 5):= by

  have eqx : (x - 2) * (x + 7) * (x - 5) = 0 := by
    ring_nf at tan
    rw [h] at tan
    linarith

  apply mul_eq_zero.mp at eqx
  cases eqx with
  | inl prod =>
    apply mul_eq_zero.mp at prod
    cases prod with
    | inl eq2 =>
      rw [sub_eq_zero] at eq2
      rw [eq2] at h
      norm_num at h
      have : y = √51 ∨ y = -√51 := by
        apply eq_or_eq_neg_of_abs_eq
        rw [←h]; symm; exact Real.sqrt_sq_eq_abs y
      left; rw [eq2, div_left_inj', div_left_inj']
      assumption; norm_num; norm_num
    | inr eq7 =>
      rw [←sub_neg_eq_add, sub_eq_zero] at eq7
      rw [eq7] at h
      norm_num at h
      have : y ^ 2 ≥ 0 := sq_nonneg y
      rw [h] at this
      linarith
  | inr eq5 =>
    rw [sub_eq_zero] at eq5
    rw [eq5] at h
    norm_num at h
    have : y = √285 ∨ y = -√285 := by
      apply eq_or_eq_neg_of_abs_eq
      rw [←h]; symm; exact Real.sqrt_sq_eq_abs y
    right; rw [eq5, div_left_inj', div_left_inj']
    assumption; norm_num; norm_num
