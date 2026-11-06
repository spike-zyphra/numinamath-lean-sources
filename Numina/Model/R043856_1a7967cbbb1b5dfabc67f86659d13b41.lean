import Mathlib

theorem algebra_26024 {m n : ℤ} (h : (9 + Real.sqrt 11)^2 + m * (9 + Real.sqrt 11) + n = 0) :
    m + n = 52 := by
  have h1 : (9 + Real.sqrt 11) ^ 2 = 92 + 18 * Real.sqrt 11 := by
    nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show 0 ≤ (11 : ℝ) by norm_num)]
  rw [h1] at h
  have eqco : (92 : ℝ) + (18 + (m : ℝ)) * Real.sqrt 11 + 9 * (m : ℝ) + (n : ℝ) = 0 := by
    ring_nf at h ⊢
    linarith
  have h51 : (18 + (m : ℝ)) = 0 := by
    by_contra! hh 
    have eq1 : Real.sqrt 11 = (- ( (92 : ℝ) + 9 * (m : ℝ) + (n : ℝ) ) / (18 + (m : ℝ)) ) := by
      have eq2 : (18 + (m : ℝ)) ≠ 0 := by 
        simpa using hh
      field_simp at *
      ring_nf at eqco ⊢
      nlinarith [eqco]
    have h11 : Real.sqrt 11 > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    -- rewrite sqrt (11 : R) = eq1, derive RHS > 0.
    have h_eq1 : Real.sqrt 11 = (- ( (92 : ℝ) + 9 * (m : ℝ) + (n : ℝ) ) / (18 + (m : ℝ)) ) := eq1
    -- Show real sqrt 11 equal Rational expression. This contradicts sqrt 11 = irrational.
    have h14 : Irrational (Real.sqrt 11) := by
      native_decide
    have h13 : ¬ Irrational (Real.sqrt 11) := by
      rw [h_eq1]
      simp [h_eq1]
      <;> norm_cast
      <;> aesop
      all_goals nlinarith
    contradiction
  have h31 : (92 : ℝ) + 9 * (m : ℝ) + (n : ℝ) = 0 := by
    have eq1 : (92 : ℝ) + (18 + (m : ℝ)) * Real.sqrt 11 + 9 * (m : ℝ) + (n : ℝ) = 0 := eqco
    rw [show (18 + (m : ℝ)) = (0 : ℝ) by linarith [h51] ] at eq1
    nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
  have h7 : m = -18 := by
    have hm : (m : ℝ) = -18 := by
      linarith [h51]
    have h8 : m = -18 := by
      exact_mod_cast hm
    linarith
  have h8 : n = 70 := by
    have h9 : (n : ℝ) = (70 : ℝ) := by
      rw [show (m : ℝ) = (-18 : ℝ) by 
        exact_mod_cast h7
      ] at h31
      linarith
    have h4 : n = 70 := by
      exact_mod_cast h9
    linarith
  omega