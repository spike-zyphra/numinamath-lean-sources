import Mathlib

open BigOperators Real Set

theorem algebra_224790 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, (x*y + 2*y*z)/(x^2 + y^2 + z^2) = t ∧ ¬(x=0 ∧ y=0 ∧ z=0)} (Real.sqrt 5 / 2) := by
  constructor
  · -- Show that sqrt(5)/2 is in the set
    use 1, Real.sqrt 5, 2
    constructor
    · -- Show that (1* sqrt(5) + 2*sqrt(5)*2) / (1^2 + (sqrt(5))^2 + 2^2) = sqrt(5)/2
      have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      field_simp [h1]
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5]
    · -- Show that ¬(1=0 ∧ Real.sqrt 5=0 ∧ 2=0)
      norm_num
  · -- Show that sqrt(5)/2 is greatest
    intro t ht
    rcases ht with ⟨x, y, z, ht_eq, hne⟩
    have h1 : x^2 + y^2 + z^2 > 0 := by
      by_contra h
      push_neg at h
      have h2 : x^2 ≥ 0 := sq_nonneg x
      have h3 : y^2 ≥ 0 := sq_nonneg y
      have h4 : z^2 ≥ 0 := sq_nonneg z
      have h5 : x^2 + y^2 + z^2 ≥ 0 := by linarith
      have h6 : x^2 + y^2 + z^2 = 0 := by linarith
      have h7 : x^2 = 0 := by
        linarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      have h8 : y^2 = 0 := by
        linarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      have h9 : z^2 = 0 := by
        linarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      have hx0 : x = 0 := by
        rw [sq_eq_zero_iff] at h7
        exact h7
      have hy0 : y = 0 := by
        rw [sq_eq_zero_iff] at h8
        exact h8
      have hz0 : z = 0 := by
        rw [sq_eq_zero_iff] at h9
        exact h9
      have h0 : x = 0 ∧ y = 0 ∧ z = 0 := ⟨hx0, hy0, hz0⟩
      exfalso
      tauto
    have h2 : (x * y + 2 * y * z) ≤ Real.sqrt 5 / 2 * (x^2 + y^2 + z^2) := by
      have h3 : Real.sqrt 5 > 0 := by
        positivity
      have h4 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h5 : Real.sqrt 5 * (x^2 + y^2 + z^2) ≥ 2 * (x * y + 2 * y * z) := by
        nlinarith [Real.sqrt_nonneg 5, sq_nonneg (x - y / Real.sqrt 5), sq_nonneg (2 * y - Real.sqrt 5 * z), sq_nonneg (x * Real.sqrt 5 - y), sq_nonneg (z * Real.sqrt 5 - 2 * y), sq_nonneg (y ^ 2), Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5)]
      have h6 : Real.sqrt 5 * (x^2 + y^2 + z^2) ≥ 2 * (x * y + 2 * y * z) := h5
      nlinarith
    have ht_le : t ≤ Real.sqrt 5 / 2 := by
      have ht_eq' : (x * y + 2 * y * z) / (x^2 + y^2 + z^2) = t := by
        linarith [ht_eq]
      have ht_le' : (x * y + 2 * y * z) / (x^2 + y^2 + z^2) ≤ Real.sqrt 5 / 2 := by
        have h9 : (x * y + 2 * y * z) ≤ Real.sqrt 5 / 2 * (x^2 + y^2 + z^2) := h2
        have h1 : x^2 + y^2 + z^2 > 0 := h1
        apply (div_le_iff₀ (by linarith)).mpr
        linarith
      linarith [ht_eq', ht_le']
    linarith