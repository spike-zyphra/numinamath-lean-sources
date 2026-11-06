import Mathlib

theorem algebra_109
  (a b c : ℝ)
  (h₀ : a + b + c = 3)
  (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 4) :
  (a ^ 2 + b ^ 2) / (2 - c) + (b ^ 2 + c ^ 2) / (2 - a) + (c ^ 2 + a ^ 2) / (2 - b) = 9 := by
    have h2 : a ^ 2 + b ^ 2 = 4 - c ^ 2 := by linarith
    have h3 : b ^ 2 + c ^ 2 = 4 - a ^ 2 := by linarith
    have h4 : c ^ 2 + a ^ 2 = 4 - b ^ 2 := by linarith

    have h5 : (a ^ 2 + b ^ 2) / (2 - c) = 2 + c := by
      rw [h2]
      have h6 : 2 - c ≠ 0 := by
        by_contra h
        have h7 : c = 2 := by linarith
        have h8 : a + b = 1 := by linarith [h₀, h7]
        have h9 : a ^ 2 + b ^ 2 = 0 := by nlinarith [h7, h8, h₁]
        have h10 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h9]
        have h11 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, h9]
        have h12 : a + b + c = 2 := by nlinarith [h10, h11, h7]
        linarith [h₀, h12]
      field_simp [h6]
      nlinarith

    have h7 : (b ^ 2 + c ^ 2) / (2 - a) = 2 + a := by
      rw [h3]
      have h8 : 2 - a ≠ 0 := by
        by_contra h
        have h9 : a = 2 := by linarith
        have h10 : b + c = 1 := by linarith [h₀, h9]
        have h11 : b ^ 2 + c ^ 2 = 0 := by nlinarith [h9, h10, h₁]
        have h12 : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, h11]
        have h13 : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c, h11]
        have h14 : a + b + c = 2 := by nlinarith [h9, h12, h13]
        linarith [h₀, h14]
      field_simp [h8]
      nlinarith

    have h15 : (c ^ 2 + a ^ 2) / (2 - b) = 2 + b := by
      rw [h4]
      have h8 : 2 - b ≠ 0 := by
        by_contra h
        have h9 : b = 2 := by linarith
        have h10 : a + c = 1 := by linarith [h₀, h9]
        have h11 : a ^ 2 + c ^ 2 = 0 := by nlinarith [h9, h10, h₁]
        have h12 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg c, h11]
        have h13 : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg c, h11]
        have h14 : a + b + c = 2 := by nlinarith [h12, h9, h13]
        linarith [h₀, h14]
      field_simp [h8]
      nlinarith

    rw [h5, h7, h15]
    linarith [h₀]