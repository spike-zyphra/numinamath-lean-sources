import Mathlib

theorem algebra_261146 {a : ℝ} (ha : ∃ n : ℕ, 0 < n ∧ n > 1 ∧ a = 1 / n) :
    a^2 < a ∧ a < 1 / a := by
  rcases ha with ⟨n, hn_pos, hn_gt, ha⟩
  have h1 : (n : ℝ) > 1 := by
    exact_mod_cast (show n > 1 from hn_gt)
  have ha2 : a = (1 / (n : ℝ)) := by
    linarith [ha]
  have ha_pos : a > 0 := by
    rw [ha2]
    positivity

  have h_a2_lt_a : a^2 < a := by 
    rw [ha2]
    have h2 : (n : ℝ) > 0 := by linarith
    -- Show $\left( \frac{1}{n} \right)^2 < \frac{1}{n}$
    have h3 : (1 / (n : ℝ)) ^ 2 < (1 / (n : ℝ)) := by 
      have h4 : (1 / (n : ℝ)) ^ 2 - (1 / (n : ℝ)) < 0 := by 
        have h5 : (1 / (n : ℝ)) ^ 2 - (1 / (n : ℝ)) = ((1 - (n : ℝ)) / (n : ℝ) ^ 2) := by 
          field_simp 
          <;> ring 
        rw [h5] 
        apply div_neg_of_neg_of_pos 
        · -- Numerator is negative 
          have h6 : (1 - (n : ℝ)) < 0 := by linarith 
          linarith 
        · -- Denominator is positive 
          positivity 
      linarith 
    linarith
  -- Prove $a < 1/a$
  have ha_lt_one_div_a : a < 1 / a := by 
    rw [ha2]
    have h12 : (n : ℝ) > 1 := h1
    -- Show $\frac{1}{n} < n$
    have h13 : (1 / (n : ℝ)) < 1 / ( (1 / (n : ℝ)) ) := by 
      have h15 : 1 / ( (1 / (n : ℝ)) ) = (n : ℝ) := by 
        field_simp 
      rw [h15] 
      have h16 : (1 / (n : ℝ) ) - (n : ℝ) < 0 := by 
        have h17 : (1 / (n : ℝ) ) - (n : ℝ) = (1 - (n : ℝ) ^ 2) / (n : ℝ) := by 
          field_simp 
          <;> ring 
        rw [h17] 
        apply div_neg_of_neg_of_pos 
        · -- Numerator is negative 
          have h18 : (1 - (n : ℝ) ^ 2 ) < 0 := by 
            have h19 : (n : ℝ) ^ 2 > 1 := by nlinarith 
            nlinarith 
          linarith 
        · -- Denominator is positive 
          positivity 
      have h18 : (1 / (n : ℝ) ) < (n : ℝ) := by linarith 
      linarith 
    have h11 : (1 / (n : ℝ)) < 1 / ( (1 / (n : ℝ)) ) := h13
    linarith [h11]
  -- Show the conjunction of both parts
  constructor
  · exact h_a2_lt_a
  · exact ha_lt_one_div_a