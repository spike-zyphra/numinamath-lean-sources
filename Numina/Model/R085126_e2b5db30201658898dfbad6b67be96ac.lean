import Mathlib

theorem algebra_165520 (z : ℝ) (hz : z^2 - z + 1 ≠ 0 ∧ z^2 - z - 2 ≠ 0) :
    (z^2 - z) / (z^2 - z + 1) - (z^2 - z + 2) / (z^2 - z - 2) = 1 ↔ z = 0 ∨ z = 1 := by
  constructor
  · -- Forward direction: equation implies z=0 or z=1
    intro h
    have h1 : z^2 - z + 1 ≠ 0 := hz.1
    have h2 : z^2 - z - 2 ≠ 0 := hz.2
    have eq1 : (z^2 - z) * (z^2 - z - 2) - (z^2 - z + 2) * (z^2 - z + 1) = (z^2 - z + 1) * (z^2 - z - 2) := by 
      field_simp [h1, h2] at h ⊢
      linarith
    have eq2 : (z^2 - z) * (z^2 - z + 4) = 0 := by
      nlinarith [eq1]
    cases' (mul_eq_zero.mp eq2) with h4 h5
    · -- Case where z^2 - z = 0
      have h5 : z * (z - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case where z = 0
        left
        exact h6
      · -- Case where z - 1 = 0, so z = 1
        right
        linarith
    · -- Case where z^2 - z + 4 = 0
      have h6 : z^2 - z + 4 > 0 := by
        nlinarith [sq_nonneg (z - 1 / 2)]
      nlinarith [h6, h5]
  · -- Backward direction: z=0 or z=1 implies equation
    rintro (h | h)
    · -- Case where z = 0
      rw [h]
      norm_num
    · -- Case where z = 1
      rw [h]
      norm_num