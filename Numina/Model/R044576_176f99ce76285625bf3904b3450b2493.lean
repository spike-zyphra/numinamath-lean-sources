import Mathlib

open Real Set

theorem algebra_241174 :
  IsLeast {f | ∃ x y : ℝ, f = (x - y)^2 + (x + 1 / y + 1)^2} (1 / 2) := by 
  constructor
  · -- Show 1/2 is in the set
    use -1/2, -1
    norm_num
  · -- Show 1/2 is the minimum 
    intro r hr
    rcases hr with ⟨x, y, h_eq⟩
    have h1 : (x - y) ^ 2 + (x + 1 / y + 1) ^ 2 ≥ 1 / 2 := by
      by_cases h5 : y = 0 
      · -- A case where y = 0.
        rw [h5] 
        have h3 : 1 / (0 : ℝ) = 0 := by 
          norm_num 
        rw [h3] 
        nlinarith [sq_nonneg (x + 1 / 2)]
      · -- When y ≠ 0
        have h14 : y ≠ 0 := h5
        have h18 : (x - y) ^ 2 + (x + 1 / y + 1) ^ 2 ≥ 1 / 2 := by
          have h30 : (x - y) ^ 2 + (x + 1 / y + 1) ^ 2 =
              ((x - y) ^ 2 * y ^ 2 + (x * y + 1 + y) ^ 2) / y ^ 2 := by
            field_simp
            <;> ring
          rw [h30] 
          have h31 : ((x - y) ^ 2 * y ^ 2 + (x * y + 1 + y) ^ 2) ≥ (1 / 2) * y ^ 2 := by
            have h31 : y ≠ 0 := h14
            nlinarith [sq_nonneg ( (x - y) * y + (x * y + 1 + y) ), sq_nonneg (y + 1), sq_nonneg (x * y + 1 + y + 1 / 2), sq_nonneg ( (x + 1 / 2) * y + (y + 1) / 2 ), sq_pos_of_ne_zero (show y ≠ 0 by exact h14 ), sq_nonneg ( (x + (y + 1) / 2 ) ) ]
          have h32 : ((x - y) ^ 2 * y ^ 2 + (x * y + 1 + y) ^ 2) / y ^ 2 ≥ 1/2 := by
            have h40 : y ^ 2 > 0 := by
              apply sq_pos_of_ne_zero
              exact h14
            apply (le_div_iff₀ (by linarith)).mpr
            nlinarith 
          linarith 
        linarith
    linarith [h_eq, h1]