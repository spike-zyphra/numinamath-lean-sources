import Mathlib

open Real Set
open scoped Real

theorem calculus_22211 (x : ℝ) (hx : cos x ≠ 0) (h : cos (3 * x) / cos x = 1 / 3) :
    sin (3 * x) / sin x = 7 / 3 := by
  have h1 : cos (3 * x) = 1 / 3 * cos x := by
    have h2 : cos x ≠ 0 := hx
    field_simp [h2] at h ⊢
    linarith
  have h2 : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
    rw [cos_three_mul]
 
  rw [h2] at h1
  have h3 : cos x * (12 * cos x ^ 2 - 10) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case cos x = 0, which contradicts hx
    exfalso
    exact hx h4
  · -- Case 12 * cos x ^ 2 - 10 = 0
    have h6 : cos x ^ 2 = 5 / 6 := by
      nlinarith
    have h7 : sin x ^ 2 = 1 / 6 := by
      have h7 : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      nlinarith [h6]
    have h8 : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
      rw [sin_three_mul]
    by_cases h9 : sin x = 0
    · -- Case sin x = 0, which contradicts sin x ^ 2 = 1 / 6
      have h10 : sin x ^ 2 = 0 := by
        rw [h9]
        norm_num
      nlinarith [h7]
    · -- Case sin x ≠ 0
      have h11 : sin (3 * x) / sin x = 3 - 4 * sin x ^ 2 := by
        rw [h8]
        field_simp [h9]
        <;> ring
      rw [h11]
      nlinarith [h7]