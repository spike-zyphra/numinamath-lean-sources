import Mathlib

theorem algebra_241361 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 4^(x + y) = z) (h2 : z^((1 : ℝ)/x) * z^((1 : ℝ)/y) = 1024) :
    x / y + y / x = 3 := by
  have h3 : z ^ ((1 : ℝ) / x) * z ^ ((1 : ℝ) / y) = z ^ ((1 / x + 1 / y) : ℝ) := by 
    rw [← Real.rpow_add]
    ring_nf
    all_goals linarith
  rw [h3] at h2
  have h4 : (1 / x + 1 / y : ℝ) = (x + y) / (x * y) := by
    field_simp
    <;> ring
  rw [h4] at h2
  have h5 : z = (4 : ℝ) ^ (x + y) := by
    linarith [h1]
  rw [h5] at h2
  have h6 : ((4 : ℝ) ^ (x + y) ) ^ ((x + y) / (x * y) ) = (4 : ℝ) ^ ((x + y) * ((x + y) / (x * y) )) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  rw [h6] at h2
  have h11 : (4 : ℝ) ^ ((x + y) * ((x + y) / (x * y) ) ) = (4 : ℝ) ^ (5 : ℝ) := by
    have h1024 : (4 : ℝ) ^ ((x + y) * ((x + y) / (x * y) ) ) = (1024 : ℝ) := by
      linarith [h2]
    have h1024_eq : (1024 : ℝ) = (4 : ℝ) ^ (5 : ℝ) := by norm_num
    rw [h1024_eq] at h1024
    linarith
  have h8 : (x + y) * ((x + y) / (x * y) ) = (5 : ℝ) := by
    by_cases h : (x + y) * ((x + y) / (x * y) ) < (5 : ℝ)
    · -- Assume (x + y) * ((x + y) / (x * y) ) < 5 
      have h10 : (4 : ℝ) ^ ((x + y) * ((x + y) / (x * y) ) ) < (4 : ℝ) ^ (5 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt 
        all_goals 
          nlinarith 
      nlinarith 
    · -- If not < 5, may be greater
      by_cases h' : (x + y) * ((x + y) / (x * y) ) > (5 : ℝ)
      · -- Assume (x + y) * ((x + y) / (x * y) ) > 5 
        have h10 : (4 : ℝ) ^ ((x + y) * ((x + y) / (x * y) ) ) > (4 : ℝ) ^ (5 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt 
          all_goals 
            nlinarith 
        nlinarith 
      · -- Must be equal 
        have h9 : (x + y) * ((x + y) / (x * y) ) = (5 : ℝ) := by 
          nlinarith 
        linarith
  have h9 : (x + y) ^ 2 = 5 * (x * y) := by
    have hexp : (x + y) * ( (x + y) / (x * y) ) = 5 := by 
      linarith [h8]
    have h10 : (x + y) * ( (x + y) / (x * y) ) = ((x + y) ^ 2 ) / (x * y) := by 
      field_simp 
      <;> ring 
    rw [h10] at hexp 
    have h11 : 0 < (x * y : ℝ) := by 
      nlinarith 
    have h12 : ((x + y) ^ 2 ) / (x * y) = (5 : ℝ) := by 
      linarith [hexp]
    have h13 : (x + y) ^ 2 = 5 * (x * y) := by
      field_simp [show (x * y : ℝ) ≠ 0 by nlinarith] at h12 ⊢ 
      nlinarith 
    linarith [h13]
  have h10 : x ^ 2 + y ^ 2 = 3 * (x * y) := by
    nlinarith [h9]
  have h11 : x / y + y / x = (x ^ 2 + y ^ 2 ) / (x * y) := by 
    field_simp 
    <;> ring 
  rw [h11]
  have h12 : (x ^ 2 + y ^ 2 ) / (x * y ) = 3 := by
    have h13 : x * y ≠ 0 := by
      have h14 : x ≠ 0 := by linarith
      have h15 : y ≠ 0 := by linarith
      exact mul_ne_zero h14 h15
    have h14 : x ^ 2 + y ^ 2 = 3 * (x * y) := by 
      linarith [h10]
    have h15 : (x ^ 2 + y ^ 2 ) / (x * y) = 3 := by
      have h17 : x ^ 2 + y ^ 2 = 3 * (x * y) := h14
      have h18 : x * y ≠ 0 := h13
      field_simp [h18] 
      linarith 
    exact h15 
  linarith [h12]