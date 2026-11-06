import Mathlib

theorem algebra_235806 (a b : ℤ) : a^2 + b^2 + 50 = 8 * a + 12 * b ↔
    (a, b) = (3, 5) ∨ (a, b) = (3, 7) ∨ (a, b) = (5, 5) ∨ (a, b) = (5, 7) := by
  constructor
  · -- Prove that if the equation holds, then (a,b) is one of the four pairs.
    intro h
    have h1 : a^2 + b^2 + 50 = 8 * a + 12 * b := h
    have h2 : (a - 4 : ℤ) ^ 2 + (b - 6 : ℤ) ^ 2 = 2 := by
      nlinarith [h1]
    have h4 : (a - 4 : ℤ) ≥ -1 := by 
      nlinarith [sq_nonneg (b - 6), sq_nonneg (a - 4)]
    have h5 : (a - 4 : ℤ) ≤ 1 := by 
      nlinarith [sq_nonneg (b - 6), sq_nonneg (a - 4)]
    have h6 : (a - 4 : ℤ) = 0 ∨ (a - 4 : ℤ) = 1 ∨ (a - 4 : ℤ) = -1 := by 
      omega
    rcases h6 with (h6 | h6 | h6)
    · -- Case a - 4 = 0
      have h7 : (a - 4 : ℤ) = 0 := h6
      rw [h7] at h2
      have h8 : (b - 6 : ℤ) ^ 2 = 2 := by
        nlinarith
      exfalso
      have h9 : (b - 6 : ℤ) ≤ 1 := by nlinarith [sq_nonneg (b - 6 : ℤ), h8]
      have h10 : (b - 6 : ℤ) ≥ -1 := by nlinarith [sq_nonneg (b - 6 : ℤ), h8]
      have h11 : (b - 6 : ℤ) = 0 ∨ (b - 6 : ℤ) = 1 ∨ (b - 6 : ℤ) = -1 := by
        omega
      rcases h11 with (h | h | h)
      all_goals
        rw [h] at h8
        omega
    · -- Case a - 4 = 1
      have h7 : (a - 4 : ℤ) = 1 := h6
      rw [h7] at h2
      have h8 : (b - 6 : ℤ) ^ 2 = 1 := by
        nlinarith
      have h9 : (b - 6 : ℤ) = 1 ∨ (b - 6 : ℤ) = -1 := by
        rw [sq_eq_one_iff] at h8
        tauto
      cases h9 with
      | inl h10 =>
        have ha1 : a = 5 := by
          omega
        have hb1 : b = 7 := by
          omega
        simp [ha1, hb1]
      | inr h10 =>
        have ha1 : a = 5 := by
          omega
        have hb1 : b = 5 := by
          omega
        simp [ha1, hb1]
    · -- Case a - 4 = -1
      have h7 : (a - 4 : ℤ) = -1 := h6
      rw [h7] at h2
      have h8 : (b - 6 : ℤ) ^ 2 = 1 := by
        nlinarith
      have h9 : (b - 6 : ℤ) = 1 ∨ (b - 6 : ℤ) = -1 := by
        rw [sq_eq_one_iff] at h8
        tauto
      cases h9 with
      | inl h10 =>
        have ha1 : a = 3 := by
          omega
        have hb1 : b = 7 := by
          omega
        simp [ha1, hb1]
      | inr h10 =>
        have ha1 : a = 3 := by
          omega
        have hb1 : b = 5 := by
          omega
        simp [ha1, hb1]
  · -- Prove the converse: each pair is a solution.
    rintro (h | h | h | h)
    · -- (a, b) = (3, 5)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (a, b) = (3, 7)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (a, b) = (5, 5)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (a, b) = (5, 7)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num