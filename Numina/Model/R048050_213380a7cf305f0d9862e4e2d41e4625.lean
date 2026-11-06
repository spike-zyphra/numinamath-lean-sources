import Mathlib

theorem algebra_241159 : (Complex.I + 1) ^ 2016 + (Complex.I - 1) ^ 2016 = 2 ^ 1009 := by
  have h1 : (Complex.I + 1) ^ 4 = -4 := by
    calc
      (Complex.I + 1) ^ 4 = ((Complex.I + 1) ^ 2) ^ 2 := by ring
      _ = (2 * Complex.I) ^ 2 := by
        have h1 : (Complex.I + 1) ^ 2 = 2 * Complex.I := by
          calc
            (Complex.I + 1) ^ 2 = Complex.I ^ 2 + 2 * Complex.I + 1 := by ring
            _ = -1 + 2 * Complex.I + 1 := by simp [Complex.I_sq]
            _ = 2 * Complex.I := by ring
        rw [h1]
      _ = -4 := by
        calc
          (2 * Complex.I) ^ 2 = 4 * (Complex.I ^ 2) := by ring
          _ = 4 * (-1) := by simp [Complex.I_sq]
          _ = -4 := by ring

  have h2 : (Complex.I - 1) ^ 4 = -4 := by
    calc
      (Complex.I - 1) ^ 4 = ((Complex.I - 1) ^ 2) ^ 2 := by ring
      _ = (-2 * Complex.I) ^ 2 := by
        have h2 : (Complex.I - 1) ^ 2 = -2 * Complex.I := by
          calc
            (Complex.I - 1) ^ 2 = Complex.I ^ 2 - 2 * Complex.I + 1 := by ring
            _ = -1 - 2 * Complex.I + 1 := by simp [Complex.I_sq]
            _ = -2 * Complex.I := by ring
        rw [h2]
      _ = -4 := by
        calc
          (-2 * Complex.I) ^ 2 = 4 * (Complex.I ^ 2) := by ring
          _ = 4 * (-1) := by simp [Complex.I_sq]
          _ = -4 := by ring

  have h3 : (Complex.I + 1) ^ 2016 = ((Complex.I + 1) ^ 4) ^ 504 := by
    calc
      (Complex.I + 1) ^ 2016 = (Complex.I + 1) ^ (4 * 504 : ℕ) := by norm_num
      _ = ((Complex.I + 1) ^ 4) ^ 504 := by rw [pow_mul]

  have h4 : (Complex.I - 1) ^ 2016 = ((Complex.I - 1) ^ 4) ^ 504 := by
    calc
      (Complex.I - 1) ^ 2016 = (Complex.I - 1) ^ (4 * 504 : ℕ) := by norm_num
      _ = ((Complex.I - 1) ^ 4) ^ 504 := by rw [pow_mul]

  rw [h3, h4]
  rw [h1, h2]
  norm_num [pow_mul]