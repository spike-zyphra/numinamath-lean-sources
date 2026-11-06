import Mathlib

theorem algebra_100268 (m n : ℤ) (hm : 0 < m) (hn : 0 < n)
    (h : n - (m / n : ℝ) = 2011 / 3) :
    m ≥ 1120 := by 
  have h1 : (n : ℝ) - (m / n : ℝ) = (2011 / 3 : ℝ) := by 
    simpa using h
  have h2 : (n : ℝ) * (n : ℝ) - (m : ℝ) = (2011 / 3 : ℝ) * (n : ℝ) := by
    have eq1 : (n / n : ℝ) = 1 := by
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp [hn']
    have eq2 : (n : ℝ) - (m / n : ℝ) = (2011 / 3 : ℝ) := by
      linarith
    field_simp [eq1] at eq2 ⊢
    nlinarith [eq2]
  have h3 : (3 * (n : ℝ) ^ 2 - 2011 * (n : ℝ) - 3 * (m : ℝ)) = 0 := by
    linarith [h2]
  have h4 : 3 * n ^ 2 - 2011 * n - 3 * m = 0 := by
    have hk1 : (3 * (n : ℝ) ^ 2 - 2011 * (n : ℝ) - 3 * (m : ℝ)) = (0 : ℝ) := h3
    have hk2 : (3 * (n : ℝ) ^ 2 - 2011 * (n : ℝ) - 3 * (m : ℝ) : ℝ) = (3 * n ^ 2 - 2011 * n - 3 * m : ℝ) := by ring
    rw [hk2] at hk1
    have hk3 : (3 * n ^ 2 - 2011 * n - 3 * m : ℝ) = (0 : ℝ) := by
      linarith
    have hk4 : (3 * n ^ 2 - 2011 * n - 3 * m : ℤ) = 0 := by
      exact_mod_cast hk3
    linarith
  have h5 : n > 670 := by
    by_contra h
    push_neg at h
    have eq1 : 3 * m = 3 * n ^ 2 - 2011 * n := by
      nlinarith
    have eq2 : m = (3 * n ^ 2 - 2011 * n) / 3 := by
      omega
    have h7 : (3 * n ^ 2 - 2011 * n) / 3 < 0 := by
      have h8 : n ≤ 670 := by linarith
      have h9 : 3 * n ^ 2 - 2011 * n < 0 := by nlinarith
      omega
    have eq3 : m < 0 := by
      nlinarith
    linarith
  have h6 : n % 3 = 0 := by
    have eq1 : 3 * m = 3 * n ^ 2 - 2011 * n := by
      linarith
    have h5 : (3 * m : ℤ) % 3 = (3 * n ^ 2 - 2011 * n : ℤ) % 3 := by 
      omega
    have h7 : (3 * n ^ 2 - 2011 * n : ℤ) % 3 = 0 := by
      have h8 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases h8 with (h8 | h8 | h8)
      · -- case n % 3 = 0
        simp [h8, Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod]
        <;> omega
      · -- case n % 3 = 1
        simp [h8, Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod]
        <;> omega
      · -- case n % 3 = 2
        simp [h8, Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod]
        <;> omega
    have h7' : (3 * m : ℤ) % 3 = 0 := by
      omega
    omega
  have h7 : n ≥ 672 := by
    omega
  have eq1 : 3 * m = 3 * n ^ 2 - 2011 * n := by
    linarith
  nlinarith [sq_nonneg (n - 672 : ℤ), sq_nonneg (m - 1120 : ℤ)]