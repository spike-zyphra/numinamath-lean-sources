import Mathlib

theorem algebra_13984 : Complex.I ^ 6 + Complex.I ^ 16 + Complex.I ^ (-26 : ℤ) = -1 := by
  have h1 : Complex.I ^ 6 = -1 := by
    calc 
      Complex.I ^ 6 = Complex.I ^ 4 * Complex.I ^ 2 := by ring
      _ = 1 * Complex.I ^ 2 := by simp [Complex.I_sq]
      _ = 1 * -1 := by simp [Complex.I_sq]
      _ = -1 := by ring

  have h2 : Complex.I ^ 16 = 1 := by
    calc 
      Complex.I ^ 16 = (Complex.I ^ 4) ^ 4 := by ring
      _ = 1 ^ 4 := by simp [Complex.I_sq]
      _ = 1 := by norm_num
  
  have h3 : Complex.I ^ (-26 : ℤ) = -1 := by
    rw [zpow_neg, zpow_ofNat]
    have h4 : Complex.I ^ 26 = -1 := by
      calc 
        Complex.I ^ 26 = Complex.I ^ (4 * 6 + 2) := by ring
        _ = (Complex.I ^ 4) ^ 6 * Complex.I ^ 2 := by ring
        _ = 1 ^ 6 * Complex.I ^ 2 := by simp [Complex.I_sq]
        _ = 1 * Complex.I ^ 2 := by ring
        _ = 1 * (-1) := by simp [Complex.I_sq]
        _ = -1 := by ring

    simp [h4]
    all_goals norm_num
  
  rw [h1, h2, h3]
  all_goals norm_num