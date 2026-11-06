import Mathlib

theorem algebra_288663 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hsum : 56 ≤ x + y ∧ x + y ≤ 59) (hxy : 0.9 < (x / y : ℝ) ∧ (x / y : ℝ) < 0.91) :
    y^2 - x^2 = 177 := by
  have h1 : 56 ≤ x + y := hsum.1
  have h2 : x + y ≤ 59 := hsum.2
  have h3 : (x / y : ℝ) < 0.91 := hxy.2
  have h4 : 0.9 < (x / y : ℝ) := hxy.1

  have h5 : 10 * x > 9 * y := by
    by_contra h
    push_neg at h
    have h6 : (x : ℝ) / (y : ℝ) ≤ 0.9 := by
      have hf1 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast show 0 < (y : ℕ) by linarith
      have h9 : (x : ℝ) ≤ 0.9 * (y : ℝ) := by
        have h3 : (10 * x : ℝ) ≤ 9 * (y : ℝ) := by
          have h4 : (10 * x : ℝ) ≤ (9 * (y : ℝ)) := by
            have h7 : (10 * (x : ℝ) : ℝ) ≤ (9 * (y : ℝ) : ℝ) := by
              have h4' : 10 * x ≤ 9 * y := by linarith
              exact_mod_cast h4'
            nlinarith
          nlinarith
        nlinarith
      have : (x : ℝ) / (y : ℝ) ≤ (0.9 : ℝ) := by 
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    have h7 : (x / y : ℝ) ≤ (0.9 : ℝ) := by
      norm_num at h6 ⊢
      linarith
    linarith
    all_goals linarith
    all_goals linarith
  have h6 : 100 * x < 91 * y := by
    by_contra h
    push_neg at h
    have hn4 : (x : ℝ) / (y : ℝ) ≥ (0.91 : ℝ) := by
      have hf1 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast show 0 < (y : ℕ) by linarith
      have h7 : (100 * (x : ℝ) : ℝ) ≥ (91 * (y : ℝ) : ℝ) := by
        have h3 : (100 * x : ℝ) ≥ 91 * (y : ℝ) := by
          exact_mod_cast show 100 * x ≥ 91 * y by linarith
        nlinarith
      have h3' : (x : ℝ) ≥ (0.91 : ℝ) * (y : ℝ) := by
        nlinarith
      have : (x : ℝ) / (y : ℝ) ≥ (0.91 : ℝ) := by 
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    linarith
    all_goals linarith
  have h7 : x ≤ 59 := by
    omega
  have h8 : y ≤ 59 := by
    omega
  interval_cases x <;> try { 
    omega 
  }
  <;> interval_cases y 
  <;> norm_num at h5 h6 h3 h4 h1 h2 ⊢ 
  <;> omega
  <;> try { 
    all_goals norm_num 
    <;> try { 
      omega 
    }
  }