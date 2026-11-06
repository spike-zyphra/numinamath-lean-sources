import Mathlib


theorem algebra_320540 {x y : ℤ} (h : y^2 + 3 * x^2 * y^2 = 30 * x^2 + 517) : 3 * x^2 * y^2 = 588 := by
  have eq1 : y ^ 2 * (1 + 3 * x ^ 2) = 30 * x ^ 2 + 517 := by
    nlinarith
  have h1 : y % 3 = 1 ∨ y % 3 = 2 := by
    have h2 : y % 3 = 1 ∨ y % 3 = 2 ∨ y % 3 = 0 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · 
      tauto
    · 
      tauto
    ·
      -- Assume y ≡ 0 (mod 3)
      have h3 : y % 3 = 0 := by 
        omega
      have h4 : y ^ 2 % 3 = 0 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      have h5 : (30 * x ^ 2 + 517) % 3 = 1 := by
        omega
      have h6 : (y ^ 2 * (1 + 3 * x ^ 2)) % 3 = 1 := by
        omega
      have h7 : (y ^ 2 * (1 + 3 * x ^ 2)) % 3 = 0 := by
        simp [Int.mul_emod, pow_two, Int.add_emod, Int.mul_emod, h3]
      omega
  have h2 : y ^ 2 % 3 = 1 := by
    rcases h1 with (h1 | h1)
    ·
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.emod]
    ·
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.emod]
  
  have h4 : 3 * x ^ 2 + 1 ∣ 507 := by
    use (y ^ 2 - 10)
    nlinarith [sq_nonneg (y ^ 2), sq_nonneg (3 * x ^ 2 + 1), sq_nonneg (y * x * 3), sq_nonneg (y - 7), sq_nonneg (x ^ 2 - 4), sq_nonneg (3 * x ^ 2 * y ^ 2 - 600)]
  have h5 : 3 * x ^ 2 + 1 ∣ 507 := h4
  have h6 : 3 * x ^ 2 + 1 ≤ 507 := by
    apply Int.le_of_dvd (by norm_num) h5
  have h7 : 3 * x ^ 2 + 1 ≥ 1 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have h8 : x ^ 2 ≤ 169 := by
    nlinarith [h7, h6]
  have h9 : x ≤ 12 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
  have h10 : x ≥ -12 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
  interval_cases x <;> norm_num at h eq1 h2 h4 h5 h6 h7 h8 h9 h10 ⊢ 
  <;> try { 
    have h7 : y ≤ 31 := by nlinarith [sq_nonneg y, sq_nonneg x]
    have h8 : y ≥ -31 := by nlinarith [sq_nonneg y, sq_nonneg x]
    interval_cases y 
    <;> omega
  }
  <;> omega