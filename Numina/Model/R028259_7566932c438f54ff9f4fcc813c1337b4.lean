import Mathlib

open Real Set

theorem algebra_272043 :
    IsLeast {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x^2 + y^2 + 1 / x + 1 / y = 27 / 4 ∧ z = 15 / x - 3 / (4 * y)} 6 := by
  constructor
  · -- Show that 6 is in the set.
    use 2, 1 / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 6 is minimal
    intro z h
    rcases h with ⟨x, y, hx, hy, h_eq, h_eq2⟩
    have h1 : 0 < x * y := mul_pos hx hy
    have eq1 : 15 / x - 3 / (4 * y) ≥ 6 := by
      have h2 : (15 / x - 3 / (4 * y) ) - 6 ≥ 0 := by
        have h2 : (15 / x - 3 / (4 * y) ) - 6 = (60 * y - 3 * x - 24 * x * y) / (4 * x * y) := by
          field_simp
          ring
        rw [h2]
        apply div_nonneg
        have h3 : 60 * y - 3 * x - 24 * x * y ≥ 0 := by
          have h4 : x ^ 3 * y + x * y ^ 3 + y + x = (27 / 4) * x * y := by
            have h5 : x^2 + y^2 + 1 / x + 1 / y = 27 / 4 := by linarith [h_eq]
            have eq1 : (x^2 + y^2 + 1 / x + 1 / y) * (x * y) = x^3 * y + x * y^3 + y + x := by
              field_simp
              ring
            have eq2 : (x^2 + y^2 + 1 / x + 1 / y) * (x * y) = (27 / 4) * (x * y) := by
              have h10 : x^2 + y^2 + 1 / x + 1 / y = 27 / 4 := by linarith [h_eq]
              have h11 : (x^2 + y^2 + 1 / x + 1 / y) * (x * y) = (27 / 4) * (x * y) := by
                field_simp at h10 ⊢
                nlinarith
              linarith
            have h12 : x^3 * y + x * y^3 + y + x = (27 / 4) * x * y := by
              nlinarith [eq1, eq2]
            linarith
          have h5 : 60 * y - 3 * x - 24 * x * y ≥ 0 := by
            nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1 / 2), 
                      sq_nonneg (x * y - 1), sq_nonneg (x - 2 * y), sq_nonneg (x * (y - 1 / 2) - 1), 
                      sq_nonneg (y), sq_nonneg (x), 
                      mul_pos hx hy, 
                      sq_nonneg (x^2 - 4 ), sq_nonneg (y^2 - 1 / 4)
                  ]
          linarith
        linarith
        all_goals positivity
      linarith
    linarith [h_eq2, eq1]