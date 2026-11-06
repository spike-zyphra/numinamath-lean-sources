import Mathlib

theorem algebra_299621 {n : ℕ} (hn : n ≠ 0) :
    Real.sqrt (1 + 1 / n ^ 2 + 1 / (n + 1) ^ 2) = 1 + 1 / n - 1 / (n + 1) := by
  have h1 : (1 + 1 / n ^ 2 + 1 / (n + 1) ^ 2 : ℝ) = (1 + 1 / n - 1 / (n + 1) : ℝ) ^ 2 := by
    have h2 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by assumption)
    -- Need to show the real expression above is ≥ 0.
    have h3 : (n + 1 : ℝ) ≠ 0 := by
      have h4 : (n + 1 : ℝ) ≥ 1 := by
        have hn' : n ≥ 1 := by
          by_contra h 
          push_neg at h 
          have : n = 0 := by linarith 
          tauto 
        have hn'' : (n : ℝ) ≥ 1 := by
          exact_mod_cast hn'
        have h6 : (n + 1 : ℝ) ≥ 1 := by
          have hn''' : (n : ℝ) ≥ 1 := hn''
          nlinarith 
        exact h6 
      linarith
    field_simp [h2, h3]
    <;> ring_nf <;> field_simp [h2, h3] <;> ring
  rw [h1]
  have h4 : (1 + 1 / n - 1 / (n + 1) : ℝ) ≥ 0 := by
    have h2 : (n : ℝ) ≥ 1 := by 
      have hn' : n ≥ 1 := by 
        by_contra h 
        push_neg at h 
        have : n = 0 := by linarith 
        tauto 
      exact_mod_cast hn'
    have h3 : (n + 1 : ℝ) ≥ 2 := by 
      have hn' : n ≥ 1 := by 
        by_contra h 
        push_neg at h 
        have : n = 0 := by linarith 
        tauto 
      have hn'' : (n : ℝ) ≥ 1 := by 
        exact_mod_cast hn'
      nlinarith 
    have h5 : (n : ℝ) > 0 := by linarith
    have h6 : (n + 1 : ℝ) > 0 := by linarith
    have h7 : (1 + 1 / n - 1 / (n + 1) : ℝ) > 0 := by
      have h8 : (1 + 1 / n - 1 / (n + 1) : ℝ) = (n ^ 2 + n + 1) / ((n : ℝ) * (n + 1)) := by
        field_simp [show (n : ℝ) ≠ 0 by linarith, show (n + 1 : ℝ) ≠ 0 by linarith]
        <;> ring_nf
      rw [h8]
      apply div_pos
      · -- Show the numerator is positive
        nlinarith [sq_nonneg ((n : ℝ) * (n + 1)), sq_nonneg ((n : ℝ) * (n + 1) - 1)]
      · -- Show the denominator is positive
        positivity
    linarith
  rw [Real.sqrt_sq (by linarith)]