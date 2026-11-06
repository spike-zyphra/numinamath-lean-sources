import Mathlib

theorem algebra_9569 {x : ℝ} (hx : x > 0) (h : x + 1 / x = 1679) : Real.sqrt x + 1 / Real.sqrt x = 41 := by
  have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h2 : 0 < Real.sqrt x := by
    apply Real.sqrt_pos.2
    linarith
  have h3 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = 1681 := by
    have h4 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = Real.sqrt x ^ 2 + 2 + (1 / (Real.sqrt x) ^ 2 : ℝ) := by
      field_simp [h2.ne.symm]
      <;> ring_nf
      <;> nlinarith [h1]
    calc 
      (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = Real.sqrt x ^ 2 + 2 + (1 / (Real.sqrt x) ^ 2 : ℝ) := by
        rw [h4]
      _ = Real.sqrt x ^ 2 + 2 + 1 / (Real.sqrt x ^ 2 : ℝ) := by 
        norm_num
      _ = Real.sqrt x ^ 2 + 2 + 1 / x := by 
        have h5 : Real.sqrt x ^ 2 = x := h1
        rw [h5]
      _ = x + 2 + 1 / x := by 
        rw [show Real.sqrt x ^ 2 = x by linarith [h1]]
        all_goals 
          try { 
            ring_nf
            <;> norm_num
          }
          <;> try { 
            nlinarith
          }
      _ = (x + 1 / x) + 2 := by 
        field_simp
        <;> ring_nf
      _ = 1679 + 2 := by 
        rw [h]
      _ = (1681 : ℝ) := by 
        norm_num
  have h5 : Real.sqrt x + 1 / Real.sqrt x > 0 := by 
    positivity
  have h7 : (Real.sqrt 1681 : ℝ) = (41 : ℝ) := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    all_goals
      try { 
        nlinarith
      }
  have h6 : Real.sqrt x + 1 / Real.sqrt x = Real.sqrt 1681 := by
    have h8 : (Real.sqrt x + 1 / Real.sqrt x : ℝ) ^ 2 = (1681 : ℝ) := by 
      linarith [h3]
    have h8' : (Real.sqrt 1681 : ℝ) ^ 2 = (1681 : ℝ) := Real.sq_sqrt (by 
      norm_num
      all_goals 
        try { 
          ring_nf
          <;> norm_num
        }
        <;> try { 
          nlinarith
        }
    )
    have h8_non_neg : Real.sqrt x + 1 / Real.sqrt x >= 0 := by
      positivity
      all_goals
      nlinarith
    have h9 : Real.sqrt 1681 >= 0 := by 
      positivity
    nlinarith [h8, h8', h8_non_neg, Real.sqrt_nonneg 1681]
  rw [h7] at h6
  linarith [h6]