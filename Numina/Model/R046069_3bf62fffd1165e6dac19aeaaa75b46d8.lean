import Mathlib

theorem algebra_18590 : Complex.I ^ 5 + Complex.I ^ (-25 : ℤ) + Complex.I ^ 45 = Complex.I := by
  have h1 : Complex.I ^ 5 = Complex.I := by
    have h2 : Complex.I ^ 4 = 1 := by
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    calc
      Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := by ring
      _ = 1 * Complex.I := by rw [h2]
      _ = Complex.I := by ring

  have eq1 : Complex.I ^ 4 = 1 := by
    norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]

  have eq2 : Complex.I ^ (-25 : ℤ) = -Complex.I := by
    have eq3 : Complex.I ^ (-25 : ℤ) = (Complex.I ^ (25 : ℕ))⁻¹ := by
      simp [zpow_neg, zpow_ofNat]
    rw [eq3]
    have eq4 : (Complex.I ^ (25 : ℕ)) = Complex.I := by
      have h1' : Complex.I ^ 4 = 1 := eq1
      calc
        Complex.I ^ (25 : ℕ) = Complex.I ^ (4 * 6 + 1 : ℕ) := by norm_num
        _ = (Complex.I ^ 4) ^ 6 * Complex.I := by ring_nf
        _ = (1) ^ 6 * Complex.I := by rw [h1']
        _ = Complex.I := by ring_nf
    rw [eq4]
    field_simp [Complex.ext_iff, Complex.I_mul_I]

  have eq3 : Complex.I ^ (3 : ℤ) = -Complex.I := by
    simp [zpow_ofNat, pow_succ, Complex.I_mul_I, Complex.ext_iff]
    all_goals norm_num

  have eq5 : Complex.I ^ 45 = Complex.I := by
    have h1' : Complex.I ^ 4 = 1 := eq1
    calc
      Complex.I ^ 45 = Complex.I ^ (4 * 11 + 1 : ℕ) := by norm_num
      _ = (Complex.I ^ 4) ^ 11 * Complex.I := by ring_nf
      _ = (1) ^ 11 * Complex.I := by rw [h1']
      _ = Complex.I := by ring_nf

  rw [h1, eq5]
  rw [eq2]
  simp [Complex.ext_iff, add_left_inj]