import Mathlib

theorem algebra240229 :
    {(x, y) : ℝ × ℝ | (y ≠ 0 ∧ x - y = x * y ∧ x - y= x / y )∨ (y ≠ 0 ∧ x + y = x * y ∧ x + y = x / y)} = {(1 / 2, -1), (- (1 / 2), -1)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Forward
    rintro (h | h)
    · -- First case
      rcases h with ⟨hy, h1, h2⟩
      have h3 : y ≠ 0 := hy
      have h4 : (x - y) * y = x := by
        have h5 : x - y = x / y := by linarith
        have h6 : (x - y) * y = x := by
          rw [h5]
          field_simp [show y ≠ 0 by tauto]
        linarith
      have h7 : x * (1 - y) = y := by
        have h18 : x - y = x * y := by linarith
        nlinarith
      have h7a : x * (y - 1) = y ^ 2 := by
        nlinarith
      have h8 : y * (y + 1) = 0 := by
        have h14 : - (x * (y - 1)) = y := by
          have h20 : x * (1 - y) = y := h7
          have : x * (1 - y) = - (x * (y - 1)) := by ring
          rw [this] at h20
          nlinarith
        have h15 : x * (y - 1) = y ^ 2 := h7a
        nlinarith
      cases' (mul_eq_zero.mp h8) with h10 h11
      · 
        exfalso
        apply h3
        linarith
      · 
        have h13 : y = -1 := by linarith
        have h14 : x = - (1 / 2) := by
          rw [show y = -1 by linarith] at h7
          nlinarith
        simp [h14, h13]
    · -- Second case
      rcases h with ⟨hy, h1, h2⟩
      have h3 : y ≠ 0 := hy
      have h4 : (x + y) * y = x := by
        have h5 : x + y = x / y := by linarith
        have h6 : (x + y) * y = x := by
          rw [h5]
          field_simp [show y ≠ 0 by tauto]
        linarith
      have h7 : x + y = x * y := by linarith
      have h8 : x * (y ^ 2 - 1) = 0 := by
        have h19 : (x + y) * y = x := by linarith
        rw [show x + y = x * y by linarith] at h19
        nlinarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · 
        have h11 : x = 0 := by linarith
        have h12 : y = 0 := by
          rw [h11] at h7
          nlinarith
        exfalso
        apply h3
        linarith
      · 
        have h13 : y ^ 2 = 1 := by linarith
        have h14 : y = 1 ∨ y = -1 := by
          have h14 : y ^ 2 = 1 := h13
          have : y = 1 ∨ y = -1 := by
            rw [sq_eq_one_iff] at h14
            tauto
          tauto
        cases' h14 with h15 h16
        · 
          have h17 : y = 1 := by linarith
          have h18 : x + 1 = x := by 
            rw [show y = 1 by linarith] at h7
            linarith
          linarith
        · 
          have h18 : y = -1 := by linarith
          have h19 : x = 1 / 2 := by
            rw [show y = -1 by linarith] at h7
            nlinarith
          simp [h19, h18]
  · -- Backward
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · 
      right
      constructor
      · 
        norm_num
      constructor
      · 
        norm_num
      · 
        norm_num
    · 
      left
      constructor
      · 
        norm_num
      constructor
      · 
        norm_num
      · 
        norm_num