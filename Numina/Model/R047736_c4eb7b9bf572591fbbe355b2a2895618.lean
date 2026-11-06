import Mathlib
theorem algebra_604698 : {(a, b, c) : ℤ × ℤ × ℤ| a + b + c = 24 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 210 ∧ a * b * c = 440} = {(5, 8, 11), (8, 5, 11), (5, 11, 8), (11, 5, 8), (8, 11, 5), (11, 8, 5)}:= by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Forward direction: the equations hold implies (a,b,c) is a permutation of (5,8,11)
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : c = 24 - a - b := by linarith
    rw [h4] at h₂ h₃
    have h5 : a ≤ 24 := by nlinarith [sq_nonneg (a - 24), sq_nonneg (b - 24), sq_nonneg ((24 - a - b) - 24)]
    have h6 : b ≤ 24 := by nlinarith [sq_nonneg (a - 24), sq_nonneg (b - 24), sq_nonneg ((24 - a - b) - 24)]
    have h7 : a ≥ 0 := by nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg ((24 - a - b) - 0)]
    have h8 : b ≥ 0 := by nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg ((24 - a - b) - 0)]
    have h9 : (a - 5) * (a - 8) * (a - 11) = 0 := by
      nlinarith [sq_nonneg (a - 5), sq_nonneg (a - 8), sq_nonneg (a - 11), sq_nonneg (b - 5), sq_nonneg (b - 8), sq_nonneg (b - 11), sq_nonneg ((24 - a - b) - 5), sq_nonneg ((24 - a - b) - 8), sq_nonneg ((24 - a - b) - 11)]
    cases' (mul_eq_zero.mp h9) with h10 h11
    cases' (mul_eq_zero.mp h10) with h10 h12
    · -- a = 5
      have ha : a = 5 := by linarith
      rw [ha] at h₃ h₂
      have hb : b = 8 ∨ b = 11 := by
        have h16 : b * (24 - 5 - b) = 88 := by nlinarith
        have h17 : b ≤ 19 := by nlinarith
        interval_cases b <;> omega
      rcases hb with (hb | hb)
      · -- b = 8
        have hb8 : b = 8 := by linarith
        have hc11 : 24 - 5 - 8 = 11 := by nlinarith
        simp [ha, hb8, hc11] at *
        tauto
      · -- b = 11
        have hb11 : b = 11 := by linarith
        have hc8 : 24 - 5 - 11 = 8 := by nlinarith
        simp [ha, hb11, hc8] at *
        tauto
    · -- a = 8
      have ha : a = 8 := by linarith
      rw [ha] at h₃ h₂
      have hb : b = 5 ∨ b = 11 := by
        have h16 : b * (24 - 8 - b) = 55 := by nlinarith
        have h17 : b ≤ 16 := by nlinarith
        interval_cases b <;> omega
      rcases hb with (hb | hb)
      · -- b = 5
        have hb5 : b = 5 := by linarith
        have hc11 : 24 - 8 - 5 = 11 := by nlinarith
        simp [ha, hb5, hc11] at *
        tauto
      · -- b = 11
        have hb11 : b = 11 := by linarith
        have hc5 : 24 - 8 - 11 = 5 := by nlinarith
        simp [ha, hb11, hc5] at *
        tauto
    · -- a = 11
      have ha : a = 11 := by linarith
      rw [ha] at h₃ h₂
      have hb : b = 5 ∨ b = 8 := by
        have h16 : b * (24 - 11 - b) = 40 := by nlinarith
        have h17 : b ≤ 13 := by nlinarith
        interval_cases b <;> omega
      rcases hb with (hb | hb)
      · -- b = 5
        have hb5 : b = 5 := by linarith
        have hc8 : 24 - 11 - 5 = 8 := by nlinarith
        simp [ha, hb5, hc8] at *
        tauto
      · -- b = 8
        have hb8 : b = 8 := by linarith
        have hc5 : 24 - 11 - 8 = 5 := by nlinarith
        simp [ha, hb8, hc5] at *
        tauto
  · -- Backward direction: the explicit 6 tuples satisfy the equations
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- (5, 8, 11)
      constructor
      · -- a + b + c = 24
        norm_num
      constructor
      · -- a ^ 2 + b ^ 2 + c ^ 2 = 210
        norm_num
      · -- a * b * c = 440
        norm_num
    · -- (8, 5, 11)
      constructor
      · -- a + b + c = 24
        norm_num
      constructor
      · -- a ^ 2 + b ^ 2 + c ^ 2 = 210
        norm_num
      · -- a * b * c = 440
        norm_num
    · -- (5, 11, 8)
      constructor
      · -- a + b + c = 24
        norm_num
      constructor
      · -- a ^ 2 + b ^ 2 + c ^ 2 = 210
        norm_num
      · -- a * b * c = 440
        norm_num
    · -- (11, 5, 8)
      constructor
      · -- a + b + c = 24
        norm_num
      constructor
      · -- a ^ 2 + b ^ 2 + c ^ 2 = 210
        norm_num
      · -- a * b * c = 440
        norm_num
    · -- (8, 11, 5)
      constructor
      · -- a + b + c = 24
        norm_num
      constructor
      · -- a ^ 2 + b ^ 2 + c ^ 2 = 210
        norm_num
      · -- a * b * c = 440
        norm_num
    · -- (11, 8, 5)
      constructor
      · -- a + b + c = 24
        norm_num
      constructor
      · -- a ^ 2 + b ^ 2 + c ^ 2 = 210
        norm_num
      · -- a * b * c = 440
        norm_num