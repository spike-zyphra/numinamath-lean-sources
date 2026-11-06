import Mathlib

theorem algebra_1412 {p q r : ℤ} (hpqr : p > 0 ∧ q > 0 ∧ r > 0) (h : p + 1 / (q + 1 / r : ℚ) = 25 / 19) :
  q = 3 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : (p : ℚ) + 1 / (q + 1 / r : ℚ) = (25 / 19 : ℚ) := by
    exact_mod_cast h
  have hp1 : p = 1 := by
    have h2 : p < 2 := by
      by_contra h2
      push_neg at h2
      have h2' : (p : ℚ) ≥ (2 : ℚ) := by exact_mod_cast h2
      have h3 : (p : ℚ) + 1 / (q + 1 / r : ℚ) ≥ (2 : ℚ) := by linarith [show (1 / (q + 1 / r : ℚ) : ℚ) ≥ (0 : ℚ) by positivity]
      linarith
    have hp2 : p > 0 := hp
    have : p = 1 := by
      omega
    exact_mod_cast this
  rw [show (p : ℚ) = (1 : ℚ) by exact_mod_cast hp1] at h1
  have h4 : 1 + (1 / (q + 1 / r : ℚ) : ℚ) = (25 / 19 : ℚ) := by
    linarith
  have h6 : (1 / (q + 1 / r : ℚ) : ℚ) = (6 / 19 : ℚ) := by
    linarith
  have hq_eq : (q + 1 / r : ℚ) = (19 / 6 : ℚ) := by
    field_simp [(show (q + 1 / r : ℚ) ≠ 0 by
      by_contra h'
      rw [h'] at h6
      norm_num at h6
      all_goals linarith
    )] at h6 ⊢
    all_goals linarith
  -- Convert hq_eq to integer equation
  have h11 : (q * r * 6 + 6 : ℤ) = 19 * r := by
    have h12 : (q + 1 / r : ℚ) = (19 / 6 : ℚ) := hq_eq
    have h13 : (q : ℚ) * (r : ℚ) + 1 = (19 / 6 : ℚ) * (r : ℚ) := by
      have h14 : (q : ℚ) + (1 / r : ℚ) = (19 / 6 : ℚ) := by
        linarith [h12]
      field_simp [(show (r : ℚ) ≠ 0 by exact_mod_cast ne_of_gt hr)] at h14 ⊢
      nlinarith [h14]
    have h14 : (q * r * 6 + 6 : ℤ) = 19 * r := by
      have h15 : (q : ℚ) * (r : ℚ) * 6 + 6 = 19 * (r : ℚ) := by
        linarith [h13]
      norm_cast at h15 ⊢
      <;> nlinarith [show r ≥ 1 by linarith]
    exact h14
  -- From the integer equation, derive expression for r*q
  have eq2 : r * (19 - 6 * q) = 6 := by 
    nlinarith
  -- r divides 6
  have h13 : r ∣ 6 := by
    use (19 - 6 * q)
    nlinarith
  -- r divides 6, so possible values for r are 1, 2, 3, 6
  have h14 : r ≥ 1 := by linarith
  have h15 : r ≤ 6 := by
    exact Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h13
  -- Now use interval_cases to check all possibilities.
  interval_cases r <;> try { omega } <;> try { 
    exfalso
    all_goals try { tauto }
    all_goals try { linarith }
  }