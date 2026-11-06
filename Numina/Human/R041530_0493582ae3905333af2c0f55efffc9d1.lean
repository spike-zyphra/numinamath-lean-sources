import Mathlib

/- solve the equation $\sqrt{\frac{x-3}{11}}+\sqrt{\frac{x-4}{10}}+\sqrt{\frac{x-5}{9}}=\sqrt{\frac{x-11}{3}}+\sqrt{\frac{x-10}{4}}+\sqrt{\frac{x-9}{5}}$ -/
theorem algebra_178386 (x : ℝ) (hx : x ≥ 11) :
    Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) + Real.sqrt ((x - 5) / 9) =
    Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) + Real.sqrt ((x - 9) / 5) ↔ x = 14 := by
  constructor
  · -- First, prove the forward direction: if the equation holds, then x = 14
    intro h
    by_cases h14 : x = 14
    · -- Trivial case where x = 14
      exact h14
    · -- Assume x ≠ 14, we need to show that the equation cannot hold
      have hne : x ≠ 14 := by
        intro h14
        contradiction
      by_cases h14' : x > 14
      · -- Case x > 14
        have h1 : Real.sqrt ((x - 3) / 11) < Real.sqrt ((x - 11) / 3) := by
          have h11 : (x - 3) / 11 < (x - 11) / 3 := by
            linarith
          have h2 : (x - 3) / 11 ≥ 0 := by
            linarith
          have h3 : (x - 11) / 3 ≥ 0 := by
            linarith
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h2 : Real.sqrt ((x - 4) / 10) < Real.sqrt ((x - 10) / 4) := by
          have h12 : (x - 4) / 10 < (x - 10) / 4 := by
            linarith
          have h4 : (x - 4) / 10 ≥ 0 := by
            linarith
          have h5 : (x - 10) / 4 ≥ 0 := by
            linarith
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h3 : Real.sqrt ((x - 5) / 9) < Real.sqrt ((x - 9) / 5) := by
          have h13 : (x - 5) / 9 < (x - 9) / 5 := by
            linarith
          have h6 : (x - 5) / 9 ≥ 0 := by
            linarith
          have h7 : (x - 9) / 5 ≥ 0 := by
            linarith
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h4 : Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) + Real.sqrt ((x - 5) / 9) < 
          Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) + Real.sqrt ((x - 9) / 5) := by
          linarith
        linarith
      · -- Case x ≤ 14 and x ≠ 14, so x < 14
        have hle : x ≤ 14 := by
          by_contra h
          push_neg at h
          linarith
        have h2 : x < 14 := by
          by_contra h
          push_neg at h
          have h14_eq : x = 14 := by linarith
          contradiction
        have h1 : Real.sqrt ((x - 3) / 11) > Real.sqrt ((x - 11) / 3) := by
          have h11 : (x - 3) / 11 > (x - 11) / 3 := by
            linarith
          have h3 : (x - 3) / 11 ≥ 0 := by
            linarith
          have h4 : (x - 11) / 3 ≥ 0 := by
            linarith
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h2 : Real.sqrt ((x - 4) / 10) > Real.sqrt ((x - 10) / 4) := by
          have h12 : (x - 4) / 10 > (x - 10) / 4 := by
            linarith
          have h5 : (x - 4) / 10 ≥ 0 := by
            linarith
          have h6 : (x - 10) / 4 ≥ 0 := by
            linarith
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h3 : Real.sqrt ((x - 5) / 9) > Real.sqrt ((x - 9) / 5) := by
          have h13 : (x - 5) / 9 > (x - 9) / 5 := by
            linarith
          have h7 : (x - 5) / 9 ≥ 0 := by
            linarith
          have h8 : (x - 9) / 5 ≥ 0 := by
            linarith
          apply Real.sqrt_lt_sqrt
          all_goals linarith
        have h4 : Real.sqrt ((x - 3) / 11) + Real.sqrt ((x - 4) / 10) + Real.sqrt ((x - 5) / 9) > 
          Real.sqrt ((x - 11) / 3) + Real.sqrt ((x - 10) / 4) + Real.sqrt ((x - 9) / 5) := by
          linarith
        linarith
  · -- Now prove the reverse direction: if x = 14, then the equation holds
    intro h14
    rw [h14]
    have h1 : Real.sqrt ((14 - 3 : ℝ) / 11) = 1 := by
      rw [show ((14 - 3 : ℝ) / 11) = (1 : ℝ) by norm_num]
      exact Real.sqrt_one
    have h2 : Real.sqrt ((14 - 4 : ℝ) / 10) = 1 := by
      rw [show ((14 - 4 : ℝ) / 10) = (1 : ℝ) by norm_num]
      exact Real.sqrt_one
    have h3 : Real.sqrt ((14 - 5 : ℝ) / 9) = 1 := by
      rw [show ((14 - 5 : ℝ) / 9) = (1 : ℝ) by norm_num]
      exact Real.sqrt_one
    have h4 : Real.sqrt ((14 - 11 : ℝ) / 3) = 1 := by
      rw [show ((14 - 11 : ℝ) / 3) = (1 : ℝ) by norm_num]
      exact Real.sqrt_one
    have h5 : Real.sqrt ((14 - 10 : ℝ) / 4) = 1 := by
      rw [show ((14 - 10 : ℝ) / 4) = (1 : ℝ) by norm_num]
      exact Real.sqrt_one
    have h6 : Real.sqrt ((14 - 9 : ℝ) / 5) = 1 := by
      rw [show ((14 - 9 : ℝ) / 5) = (1 : ℝ) by norm_num]
      exact Real.sqrt_one
    rw [h1, h2, h3, h4, h5, h6]