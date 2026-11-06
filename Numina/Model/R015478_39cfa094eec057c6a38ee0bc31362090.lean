import Mathlib

theorem algebra_12903 : (Complex.I - 1) ^ 2020 / (Nat.floor ((2 ^ 7) ^ 11)) ^ 13 = -512 := by
  have h1 : (Complex.I - 1 : ℂ) ^ 2020 = -((2 : ℂ) ^ 1010) := by
    have h4 : (Complex.I - 1 : ℂ) ^ 4 = (-4 : ℂ) := by
      calc
        (Complex.I - 1 : ℂ) ^ 4 = ((Complex.I - 1) ^ 2) ^ 2 := by ring
        _ = (-2 * Complex.I) ^ 2 := by rw [show (Complex.I - 1 : ℂ) ^ 2 = -2 * Complex.I by
            simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
            all_goals norm_num
          ]
        _ = 4 * (Complex.I ^ 2) := by ring
        _ = 4 * (-1) := by rw [Complex.I_sq]
        _ = (-4 : ℂ) := by ring
    calc
      (Complex.I - 1 : ℂ) ^ 2020 = (Complex.I - 1 : ℂ) ^ (505 * 4) := by norm_num
      _ = ((Complex.I - 1 : ℂ) ^ 4) ^ 505 := by rw [← pow_mul]
      _ = (-4 : ℂ) ^ 505 := by rw [h4]
      _ = -((4 : ℂ) ^ 505) := by ring
      _ = -((2 : ℂ) ^ (1010 : ℕ)) := by
        have h40 : (4 : ℂ) ^ 505 = (2 : ℂ) ^ (1010 : ℕ) := by
          calc
            (4 : ℂ) ^ 505 = ((2 : ℂ) ^ 2) ^ 505 := by
              rw [show (4 : ℂ) = (2 : ℂ) ^ 2 by norm_num]
            _ = (2 : ℂ) ^ (2 * 505 : ℕ) := by rw [← pow_mul]
            _ = (2 : ℂ) ^ (1010 : ℕ) := by norm_num
        rw [h40]
  have h3 : Nat.floor ((2 ^ 7 : ℝ) ^ 11) = 2 ^ 77 := by
    norm_num [Nat.floor_eq_iff]
  rw [h3] at *
  rw [h1]
  norm_num [pow_mul, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, pow_mul, pow_add]