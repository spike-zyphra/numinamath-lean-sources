import Mathlib

theorem inequalities_253227 (x : ℝ) (hx : 4 ≤ x) :
    Real.sqrt x - Real.sqrt (x - 1) ≥ 1 / x := by
  have hx1 : 0 ≤ x := by linarith
  have hx2 : 0 ≤ x - 1 := by linarith

  have h1 : Real.sqrt x - Real.sqrt (x - 1) = 1 / (Real.sqrt x + Real.sqrt (x - 1)) := by 
    have h4 : Real.sqrt x + Real.sqrt (x - 1) ≠ 0 := by
      have h4 : 0 < Real.sqrt x := by
        apply Real.sqrt_pos.2
        nlinarith
      positivity
    field_simp
    <;> nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    all_goals nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
  rw [h1]

  have hx_pos : 0 < x := by linarith
  have h2 : Real.sqrt x + Real.sqrt (x - 1) > 0 := by
    have h4 : 0 < Real.sqrt x := by
      apply Real.sqrt_pos.2
      nlinarith
    positivity
  have h7 : Real.sqrt x + Real.sqrt (x - 1) ≤ x := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), sq_nonneg (Real.sqrt x - Real.sqrt (x - 1)), sq_nonneg (Real.sqrt x ^ 2 - (x)), sq_nonneg (Real.sqrt (x - 1) ^ 2 - (x - 1)), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x - 1)), Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1)]
  have hx_pos' : 0 < Real.sqrt x + Real.sqrt (x - 1) := by
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
  have h9 : (1 / (Real.sqrt x + Real.sqrt (x - 1)) : ℝ) ≥ (1 / (x : ℝ) : ℝ) := by 
    have h14 : (x : ℝ) ≥ (Real.sqrt x + Real.sqrt (x - 1) : ℝ) := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith), sq_nonneg (Real.sqrt x - Real.sqrt (x - 1)), sq_nonneg (Real.sqrt x ^ 2 - (x)), sq_nonneg (Real.sqrt (x - 1) ^ 2 - (x - 1)), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x - 1))]
    have h12 : (1 / (Real.sqrt x + Real.sqrt (x - 1)) : ℝ) ≥ (1 / (x : ℝ) : ℝ) := by
      have hx24 : (1 : ℝ) / (Real.sqrt x + Real.sqrt (x - 1)) - (1 : ℝ) / x ≥ 0 := by
        have hx25 : (x : ℝ) ≥ (Real.sqrt x + Real.sqrt (x - 1) : ℝ) := h14
        have hx26 : 0 < (Real.sqrt x + Real.sqrt (x - 1) : ℝ) := by positivity
        have hx27 : 0 < (x : ℝ) := by linarith
        have hx28 : (x : ℝ) - (Real.sqrt x + Real.sqrt (x - 1) : ℝ) ≥ 0 := by linarith
        have hx29 : (1 : ℝ) / (Real.sqrt x + Real.sqrt (x - 1)) - (1 : ℝ) / x =
              ((x - (Real.sqrt x + Real.sqrt (x - 1)) : ℝ) ) / (( (Real.sqrt x + Real.sqrt (x - 1) : ℝ) ) * (x : ℝ) ) := by 
                field_simp
                <;> ring_nf <;> field_simp
                <;> ring_nf
        rw [hx29]
        apply div_nonneg
        all_goals
          try { nlinarith }
          all_goals nlinarith
      linarith
    linarith
  linarith [h9]