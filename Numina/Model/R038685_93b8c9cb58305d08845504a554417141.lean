import Mathlib

theorem algebra_71960 (x y : ℕ) :
    (x * y + 2) ^ 2 = x ^ 2 + y ^ 2 ↔ (x, y) = (0, 2) ∨ (x, y) = (2, 0) := by
  constructor
  · -- Forward direction: if (xy + 2)^2 = x^2 + y^2, then (x, y) is either (0, 2) or (2, 0).
    intro h
    have h_eq : (x * y + 2) ^ 2 = x ^ 2 + y ^ 2 := h
    by_cases hx : x = 0
    · -- case where x = 0
      have : y = 2 := by
        rw [hx] at h_eq
        nlinarith
      simp [Prod.ext_iff, hx, this]
    · -- x ≠ 0, so x ≥ 1
      have hx1 : x ≥ 1 := by
        omega
      by_cases hy : y = 0
      · -- y = 0, x ≠ 0
        have : x = 2 := by
          rw [hy] at h_eq
          nlinarith
        simp [Prod.ext_iff, this, hy]
      · -- y ≠ 0, so y ≥ 1
        have hy1 : y ≥ 1 := by
          omega
        have h1 : x ≤ 2 := by
          by_contra h1
          push_neg at h1
          have h3 : (x * y + 2) ^ 2 > x ^ 2 + y ^ 2 := by
            have h2 : y ≥ 1 := by 
              omega
            have h6 : x * y ≥ 3 := by 
              nlinarith
            have h7 : (x * y + 2 : ℕ) ^ 2 > (x ^ 2 + y ^ 2 : ℕ) := by
              nlinarith [sq_nonneg ((x * y : ℕ) : ℕ), sq_nonneg ((x : ℕ) : ℕ), sq_nonneg ((y : ℕ) : ℕ), 
                sq_pos_of_pos (show 0 < (x : ℕ) by omega), sq_pos_of_pos (show 0 < (y : ℕ) by omega), 
                mul_pos (show 0 < (x : ℕ) by omega) (show 0 < (y : ℕ) by omega)
              ]
            exact h7
          nlinarith 
        have h2 : y ≤ 2 := by
          by_contra h2
          push_neg at h2
          have h4 : (x * y + 2) ^ 2 > x ^ 2 + y ^ 2 := by
            have h4 : x ≤ 2 := by 
              omega
            have h6 : (x * y + 2 : ℕ) ^ 2 > (x ^ 2 + y ^ 2 : ℕ) := by
              have hx1 : x ≥ 1 := by 
                omega
              have hy1 : y ≥ 3 := by 
                omega
              nlinarith [sq_nonneg ((x * y : ℕ) : ℕ), sq_nonneg ((x : ℕ) : ℕ), sq_nonneg ((y : ℕ) : ℕ), 
                sq_pos_of_pos (show 0 < (x : ℕ) by omega), sq_pos_of_pos (show 0 < (y : ℕ) by omega), 
                mul_pos (show 0 < (x : ℕ) by omega) (show 0 < (y : ℕ) by omega)
              ]
            exact h6
          nlinarith 
        interval_cases x <;> interval_cases y 
          <;> norm_num [Prod.ext_iff] at h_eq ⊢ 
  · -- Backward implication: (x, y) = (0, 2) or (2, 0) implies (x * y + 2) ^ 2 = x ^ 2 + y ^ 2.
    rintro (h | h)
    · -- Case (0, 2)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case (2, 0)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num