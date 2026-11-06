import Mathlib

open Real Set

theorem inequalities_83960 :
    IsGreatest {t : ℝ | ∃ x y : ℝ, (x ^ 2 + y ^ 2) ≠ 0 ∧ t = (3 * x ^ 2 + 16 * x * y + 15 * y ^ 2) / (x ^ 2 + y ^ 2)} 19 := by
  constructor
  · -- Show that 19 is achieved at (x, y) = (1, 2)
    use 1, 2
    constructor
    · norm_num
    · norm_num
  · -- Show that any other element in the set is ≤ 19
    intro t ht
    rcases ht with ⟨x, y, hxy, ht⟩
    have h1 : (3 * x ^ 2 + 16 * x * y + 15 * y ^ 2) ≤ 19 * (x ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg (x * 2 - y), sq_nonneg (x - 2 * y)]
    have h2 : (3 * x ^ 2 + 16 * x * y + 15 * y ^ 2) / (x ^ 2 + y ^ 2) ≤ 19 := by
      have h3 : x^2 + y^2 > 0 := by
        by_contra h
        push_neg at h
        have h4 : x^2 + y^2 ≤ 0 := by
          linarith
        have h5 : x^2 + y^2 = 0 := by
          linarith [sq_nonneg x, sq_nonneg y, h4]
        have h6 : x^2 ≥ 0 := sq_nonneg x
        have h7 : y^2 ≥ 0 := sq_nonneg y
        have h8 : x^2 = 0 := by 
          nlinarith
        have h9 : y^2 = 0 := by 
          nlinarith
        have hx : x = 0 := pow_eq_zero h8
        have hy : y = 0 := pow_eq_zero h9
        rw [hx, hy] at hxy
        norm_num at hxy
      apply (div_le_iff₀ h3).mpr
      nlinarith
    linarith [ht, h2]