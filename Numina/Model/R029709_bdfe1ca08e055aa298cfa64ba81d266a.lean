import Mathlib

theorem number_theory_144872 (x y : ℤ) : x ^ 4 = y ^ 2 + 2 * y + 2 ↔ (x = -1 ∧ y = -1) ∨ (x = 1 ∧ y = -1) := by
  constructor
  · -- Assume x ^ 4 = y ^ 2 + 2 * y + 2, we need to prove (x = -1 ∧ y = -1) ∨ (x = 1 ∧ y = -1)
    intro h
    have h1 : x ^ 4 = y ^ 2 + 2 * y + 2 := h
    have h2 : x ^ 4 = (y + 1) ^ 2 + 1 := by 
      nlinarith 
    have h3 : (x ^ 2 - (y + 1)) * (x ^ 2 + (y + 1)) = 1 := by 
      nlinarith [h2]
    have h4 : x ^ 2 - (y + 1) = 1 ∨ x ^ 2 - (y + 1) = -1 := by 
      apply Int.eq_one_or_neg_one_of_mul_eq_one 
      exact h3 
    rcases h4 with (h4 | h4)
    · -- x ^ 2 - (y + 1) = 1 
      have h5 : x ^ 2 + (y + 1) = 1 := by 
        nlinarith [h3, h4]
      have h6 : x ^ 2 = 1 := by 
        nlinarith 
      have h7 : x = 1 ∨ x = -1 := by 
        rw [sq_eq_one_iff] at h6 
        exact h6 
      rcases h7 with (h8 | h8)
      · -- x = 1 
        have h9 : y = -1 := by 
          nlinarith [h8, h4]
        right 
        exact ⟨h8, h9⟩ 
      · -- x = -1 
        have h9 : y = -1 := by 
          nlinarith [h8, h4]
        left 
        exact ⟨h8, h9⟩ 
    · -- x ^ 2 - (y + 1) = -1 
      have h5 : x ^ 2 + (y + 1) = -1 := by 
        nlinarith [h3, h4] 
      nlinarith [sq_nonneg (x) ]
  · -- Assume (x = -1 ∧ y = -1) ∨ (x = 1 ∧ y = -1), we need to prove x ^ 4 = y ^ 2 + 2 * y + 2
    rintro (h | h)
    · -- x = -1 ∧ y = -1 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- x = 1 ∧ y = -1 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num