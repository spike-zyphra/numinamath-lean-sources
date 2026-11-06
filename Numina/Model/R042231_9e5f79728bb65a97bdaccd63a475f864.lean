import Mathlib

theorem algebra_269287 :
    {(a, d) : ℚ × ℚ | (a - d) + a + (a + d) + (a + 2 * d) = 40 ∧ 
                      (a + d) * ((a + 2 * d)^2 / (a + d)) = 32 * a} =
    {(200/9, -220/9), (8, 4)} := by
  ext ⟨a, d⟩
  simp
  constructor 
  · -- First implication: proving if the equations hold then (a, d) is one of the solutions
    rintro ⟨h1, h2⟩ 
    have h3 : 2 * a + d = 20 := by
      linarith 
    by_cases h4 : a + d = 0 
    · -- Case a + d = 0 
      have h5 : d = -a := by 
        linarith 
      rw [h5] at h3 
      have h6 : a = 20 := by 
        linarith 
      rw [h5] at h2 
      rw [h6] at h2 
      norm_num at h2 
    · -- Case a + d ≠ 0
      have h4' : a + d ≠ 0 := h4 
      have h5 : (a + 2 * d) ^ 2 = 32 * a := by 
        have h6 : a + d ≠ 0 := h4' 
        field_simp [h6] at h2 
        nlinarith 
      have h6 : d = 20 - 2 * a := by 
        linarith 
      rw [show d = 20 - 2 * a by linarith] at h5 
      have h7 : (a - 200 / 9) * (a - 8) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h7) with h8 h9 
      · -- Case a - 200 / 9 = 0 
        have ha : a = 200 / 9 := by linarith 
        have hd : d = -220 / 9 := by 
          nlinarith 
        left 
        exact ⟨ha, hd⟩ 
      · -- Case a - 8 = 0 
        have ha : a = 8 := by linarith 
        have hd : d = 4 := by 
          nlinarith 
        right 
        exact ⟨ha, hd⟩ 
  · -- Second implication: proving the solutions satisfy the equations 
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) 
    · -- First solution 
      constructor 
      · -- Check sum 
        norm_num 
      · -- Check product 
        norm_num 
    · -- Second solution 
      constructor 
      · -- Check sum 
        norm_num 
      · -- Check product 
        norm_num