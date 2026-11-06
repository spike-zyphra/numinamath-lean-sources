import Mathlib

theorem algebra_314401 {a : ℝ} (ha : a ≥ 2009) (h : ∃ x y : ℤ, x ≠ y ∧ x^2 + Real.sqrt (a - 2009) * x + (a - 2061) / 2 = 0 ∧ y^2 + Real.sqrt (a - 2009) * y + (a - 2061) / 2 = 0) :
    a = 2013 ∨ a = 2109 := by
  rcases h with ⟨x, y, hxy, hx, hy⟩
  have hsub : (x : ℝ) ^ 2 + Real.sqrt (a - 2009) * (x : ℝ) + (a - 2061) / 2 - (y ^ 2 + Real.sqrt (a - 2009) * (y : ℝ) + (a - 2061) / 2 ) = 0 := by
    linarith [hx, hy]
  have h1 : (x - y : ℝ) ≠ 0 := by 
    by_contra h0
    have h0' : x = y := by
      have h00 : (x - y : ℝ) = 0 := by linarith
      have h01 : (x : ℝ) = (y : ℝ) := by nlinarith
      norm_cast at h01 ⊢
      all_goals omega
    tauto
  have h2 : (x + y : ℝ) + Real.sqrt (a - 2009) = 0 := by
    have h4 : ((x : ℝ) - (y : ℝ)) * ((x : ℝ) + (y : ℝ) + Real.sqrt (a - 2009)) = 0 := by
      nlinarith 
    cases (mul_eq_zero.mp h4) with
    | inl h5 => 
      exfalso
      apply h1
      linarith 
    | inr h6 => 
      linarith
  -- sqrt(a - 2009) = - (x + y) 
  have h3 : Real.sqrt (a - 2009) = -(x + y : ℝ) := by
    nlinarith 
  -- sqrt(a - 2009)^2 = a - 2009
  have h4 : (Real.sqrt (a - 2009) : ℝ) ^ 2 = a - 2009 := by
    rw [Real.sq_sqrt]
    nlinarith 
  -- So, a - 2009 = (x + y)^2
  have h5 : ((x + y : ℝ) ) ^ 2 = a - 2009 := by
    rw [h3] at h4
    nlinarith 
  -- Therefore, a = (x + y)^2 + 2009
  have h6 : a = ((x + y : ℝ) ) ^ 2 + 2009 := by
    nlinarith 
  -- From both equations, we can solve products
  have h7 : (x : ℝ) ^ 2 - (x + y : ℝ) * (x : ℝ) + (a - 2061 : ℝ) / 2 = 0 := by
    rw [show Real.sqrt (a - 2009) = -(x + y : ℝ) by nlinarith [h3]] at hx
    linarith 
  have h8 : (y : ℝ) ^ 2 - (x + y : ℝ) * (y : ℝ) + (a - 2061 : ℝ) / 2 = 0 := by
    rw [show Real.sqrt (a - 2009) = -(x + y : ℝ) by nlinarith [h3]] at hy
    linarith 
  -- From the previous equality and product expression, we get x * y
  have h9 : (x * y : ℝ) = (a - 2061) / 2 := by
    nlinarith [h7, h8]
  have eq10 : x ^ 2 + y ^ 2 = 52 := by
    have h6' : a = ((x + y : ℝ) ) ^ 2 + 2009 := by linarith [h6]
    have h9' : (x * y : ℝ) = (a - 2061 : ℝ) / 2 := by linarith [h7, h8]
    have h52 : (a - 2061 : ℝ) = 2 * (x * y : ℝ) := by
      nlinarith
    have h53 : ((x + y) : ℝ) ^ 2 - 2 * (x * y : ℝ) = 52 := by
      nlinarith [h6', h52, sq_nonneg (x + y : ℝ), sq_nonneg ((x : ℝ) - (y : ℝ))]
    norm_cast at h53 ⊢
    <;> try { norm_num at h53 ⊢ }
    <;> try { nlinarith }
  -- The integer solutions to x^2 + y^2 = 52 are:
  -- (x, y) = (±4, ±6), (±6, ±4)
  -- Let's compute a for these solutions.
  -- a = (x + y)^2 + 2009
  have h71 : x ≤ 7 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), eq10]
  have h72 : x ≥ -7 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), eq10]
  have h73 : y ≤ 7 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), eq10]
  have h74 : y ≥ -7 := by
    nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), eq10]
  interval_cases x <;> try { 
    omega 
  } <;> norm_num at eq10 hxy <;> try { 
    omega 
  } <;> interval_cases y
  <;> norm_num at eq10 hxy
  <;> try { 
    norm_num [h6] at *
    <;> norm_num 
    <;> try { linarith } 
    <;> try { tauto }
  }
  <;> try { 
    exfalso 
    all_goals linarith 
  }
  <;> try { 
    tauto 
  }
  <;> try { 
    nlinarith 
  }
  <;> try { 
    nlinarith 
    all_goals linarith 
  }
  <;> try { 
    tauto 
    all_goals linarith 
  }
  all_goals linarith 
  <;> norm_num 
  <;> try { tauto }
  all_goals try { nlinarith }
  all_goals try { 
    exfalso 
    all_goals linarith 
  }
  <;> try { 
    tauto 
  }
  all_goals try { 
    ring_nf 
    <;> try { tauto } 
    all_goals nlinarith 
  }