import Mathlib

theorem algebra_326740 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (h1 : (a^2012 - c^2012) * (a^2012 - d^2012) = 2012)
    (h2 : (b^2012 - c^2012) * (b^2012 - d^2012) = 2012) :
    (a * b)^2012 - (c * d)^2012 = -2012 := by
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have hd1 : 0 < d := hd

  have h3 : a^2012 - b^2012 ≠ 0 := by
    have hab : a ≠ b := hdist.1
    have h3 : a^2012 - b^2012 ≠ 0 := by
      by_contra h
      have : a^2012 = b^2012 := by linarith
      have : a = b := by
        have h1 : a ^ 2012 = b ^ 2012 := by linarith
        have h2 : a = b := by
          have h3 : a ^ 2012 = b ^ 2012 := h1
          rw [pow_left_inj (by linarith) (by linarith) (by norm_num)] at h3
          all_goals
            try tauto
            try nlinarith
          all_goals
            try nlinarith
        assumption
      contradiction
    assumption

  -- Subtracting the equations h1 - h2 = 0, we factor and find a sum equality
  have eq1 : (a^2012 - c^2012) * (a^2012 - d^2012) - (b^2012 - c^2012) * (b^2012 - d^2012) = 0 := by
    nlinarith

  have eq2 : (a^2012 - b^2012) * (a^2012 + b^2012 - c^2012 - d^2012) = 0 := by
    nlinarith

  have h_eq : a^2012 + b^2012 = c^2012 + d^2012 := by
    apply_fun (fun x => x / (a^2012 - b^2012)) at eq2
    field_simp [h3] at eq2
    linarith
    all_goals
      try nlinarith

  -- Now expanding h1 and substituting the sum equality will give the product difference
  have h_eq2 : a^2012 * b^2012 = c^2012 * d^2012 - 2012 := by
    nlinarith [sq_pos_of_ne_zero (show (a^2012 - b^2012) ≠ 0 by 
      have hab := h3
      simpa using hab), 
    pow_pos ha 2012, pow_pos hb 2012, pow_pos hc 2012, pow_pos hd 2012, sq_nonneg (a^2012 - b^2012), sq_nonneg (c^2012 - d^2012)
  ]
  -- Now we can compute the desired value
  calc
    (a * b)^2012 - (c * d)^2012
      = (a ^ 2012) * (b ^ 2012) - (c^2012 * d^2012) := by
        ring_nf
    _ = (c^2012 * d^2012 - 2012) - (c^2012 * d^2012) := by 
        rw [show (a ^ 2012) * (b ^ 2012) = c^2012 * d^2012 - 2012 by linarith [h_eq2]]
        all_goals
         ring_nf
    _ = -2012 := by
      ring_nf