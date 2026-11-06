import Mathlib

/- Evaluate $i^5+i^{-25}+i^{45}$. -/
theorem algebra_18590 : Complex.I ^ 5 + Complex.I ^ (-25 : ℤ) + Complex.I ^ 45 = Complex.I := by
  -- notice that i^5 = i
  have h1: Complex.I ^ 5 = Complex.I := by
    rw [pow_succ]
    have: Complex.I ^ 4 = 1 := by
      simp
    rw [this]; simp
  -- i^(-5) = -1
  have h2: Complex.I ^ (-5:ℤ) = -Complex.I := by
    have hh1: Complex.I ^ (-5:ℤ) * Complex.I ^ (5:ℤ) = 1 := by
      have: Complex.I ^ (5:ℤ) ≠ 0 := by
        exact pow_ne_zero 5 (by simp)
      field_simp [this]
    have hh2: Complex.I ^ (5:ℤ) = Complex.I ^ 5 := rfl
    rw [hh2, h1] at hh1
    have hh3: Complex.I ^ (-5:ℤ) = 1 / Complex.I := by
      exact eq_one_div_of_mul_eq_one_left hh1
    rw [hh3]
    field_simp
  -- i^(-25) = i^(-5)^5
  have h3': Complex.I ^ (-25:ℤ) = (Complex.I ^ (-5:ℤ))^5 := by
    have: (-25:ℤ) = -5 * 5 := by ring
    rw [this]
    rw [zpow_mul]
    simp
    exact rfl
  -- and (i^(-5))^5 = (-i)^5 = -1 * i^5 = -i
  have h3: Complex.I ^ (-25:ℤ) = - Complex.I := by
    rw [h3', h2]
    have tt1: (-Complex.I)^5 = (-1)^5 * (Complex.I)^5 := by
      have: -Complex.I = -1 * Complex.I := by simp
      rw [this]
      exact mul_pow (-1) Complex.I 5
    rw [tt1]
    have: (-1:ℂ)^5 = -1 := by
      apply Odd.neg_one_pow
      exact Nat.odd_iff.mpr rfl
    rw [this, h1]; simp
  -- and i^45 = (i^5)^9 = i ^ 9 = (i^4)^2 * i = i
  have h4: Complex.I ^ 45 = Complex.I := by
    have tt1: 45 = 5 * 9 := by ring
    rw [tt1, pow_mul, h1]
    have tt2: 9 = 4*2+1 := by ring
    rw [tt2, pow_add, pow_mul]
    have tt3: Complex.I ^ 4 = 1 := by simp
    rw [tt3]; simp
  -- so result is i-i+i = i
  rw [h1, h3, h4]
  simp