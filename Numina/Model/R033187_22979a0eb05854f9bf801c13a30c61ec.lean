import Mathlib
theorem algebra_604272 : {(x, y, z) : ℝ × ℝ × ℝ | x + y - z = -1 ∧ x ^ 2 - y ^ 2 + z ^ 2 = 1 ∧ -x ^ 3 + y ^ 3 + z ^ 3 = -1} = {(1, -1, 1), (-1, -1, -1)}:= by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First direction: system implies the two solutions
    rintro ⟨h₁, h₂, h₃⟩
    have h : z = x + y + 1 := by linarith 
    rw [show z = x + y + 1 by linarith] at h₂
    have h4 : (x + y) * (x + 1) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h4) with hy hx
    · 
      have hy' : y = -x := by linarith 
      have hz1 : z = 1 := by 
        rw [show z = x + y + 1 by linarith] 
        rw [hy']
        linarith 
      rw [hz1] at h₃ 
      rw [hy'] at h₃
      have hx1 : x = 1 := by 
        have h5 : -x ^ 3 + (-x) ^ 3 + (1 : ℝ) ^ 3 = -1 := by linarith
        have h6 : x^3 = 1 := by
          nlinarith 
        have h7 : x = 1 := by
          have h8 : x^3 - 1 = 0 := by
            linarith 
          have h9 : (x - 1) * (x ^ 2 + x + 1) = 0 := by 
            nlinarith 
          cases' (mul_eq_zero.1 h9) with h10 h11 
          · 
            linarith 
          · 
            have h12 : (x + 1 / 2) ^ 2 ≥ 0 := by 
              apply sq_nonneg 
            nlinarith 
        exact_mod_cast h7 
      left 
      simp [hx1, hy', hz1] 
    · 
      have hx1 : x = -1 := by linarith 
      have hz2 : z = y := by 
        rw [show z = x + y + 1 by linarith] 
        rw [hx1]
        linarith 
      rw [hx1] at h₃
      rw [hz2] at h₃
      have hy1 : y = -1 := by
        have h5 : -(-1 : ℝ) ^ 3 + y ^ 3 + y ^ 3 = -1 := by linarith
        have h6 : y ^ 3 = -1 := by
          nlinarith 
        have h7 : y = -1 := by
          have h8 : y ^ 3 + 1 = 0 := by
            linarith 
          have h9 : (y + 1) * (y ^ 2 - y + 1) = 0 := by 
            nlinarith 
          cases' (mul_eq_zero.1 h9) with h10 h11 
          · 
            linarith 
          · 
            have h12 : (y - 1 / 2) ^ 2 ≥ 0 := by 
              apply sq_nonneg 
            nlinarith 
        exact_mod_cast h7 
      right 
      simp [hx1, hy1, hz2] 
  · -- Backward direction: two solutions satisfy the system.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · 
      constructor 
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · 
      constructor 
      · norm_num 
      constructor
      · norm_num 
      · norm_num