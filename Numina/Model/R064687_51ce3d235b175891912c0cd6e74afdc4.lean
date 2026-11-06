import Mathlib

theorem algebra_11457 : Complex.I ^ 14762 + Complex.I ^ 14763 + Complex.I ^ 14764 + Complex.I ^ 14765 = 0 := by
  have h1 : Complex.I ^ 14762 = -1 := by 
    have h1 : Complex.I ^ 2 = -1 := by 
      simp [Complex.I_sq]
    calc
      Complex.I ^ 14762 = Complex.I ^ (2 * 7381) := by ring
      _ = (Complex.I ^ 2) ^ 7381 := by ring
      _ = (-1) ^ 7381 := by rw [h1]
      _ = -1 := by norm_num
  have h2 : Complex.I ^ 14763 = -Complex.I := by 
    have h1 : Complex.I ^ 3 = -Complex.I := by 
      simp [pow_succ, Complex.I_sq]
    calc
      Complex.I ^ 14763 = Complex.I ^ (4 * 3690 + 3) := by norm_num
      _ = (Complex.I ^ 4) ^ 3690 * Complex.I ^ 3 := by ring
      _ = 1 ^ 3690 * Complex.I ^ 3 := by simp [Complex.I_sq]
      _ = Complex.I ^ 3 := by ring
      _ = -Complex.I := by exact h1
  have h3 : Complex.I ^ 14764 = 1 := by 
    have h1 : Complex.I ^ 4 = 1 := by 
      simp [Complex.I_sq]
    calc
      Complex.I ^ 14764 = Complex.I ^ (4 * 3691) := by norm_num
      _ = (Complex.I ^ 4) ^ 3691 := by ring
      _ = 1 ^ 3691 := by rw [h1]
      _ = 1 := by norm_num
  have h4 : Complex.I ^ 14765 = Complex.I := by 
    have h1 : Complex.I ^ 4 = 1 := by 
      simp [Complex.I_sq]
    calc
      Complex.I ^ 14765 = Complex.I ^ (4 * 3691 + 1) := by norm_num
      _ = (Complex.I ^ 4) ^ 3691 * Complex.I := by ring
      _ = 1 ^ 3691 * Complex.I := by rw [h1]
      _ = Complex.I := by ring
  rw [h1, h2, h3, h4]
  ring