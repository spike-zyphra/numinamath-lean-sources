import Mathlib

theorem algebra_271024 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = 1 / 2 + Real.sqrt (f x - (f x)^2)) (hf : f (-1) = 1 / 2) :
    f 2007 = 1 / 2 := by
  have h1 : ∀ n : ℕ, f ((↑n : ℝ) * 2 - 1) = 1 / 2 := by
    intro n 
    induction n with
    | zero =>
      norm_num at *
      all_goals 
        linarith [hf]
    | succ n ih =>
      have h2 : f ((↑(n : ℕ) : ℝ) * (2 : ℝ) - 1 : ℝ) = 1 / 2 := by 
        simpa using ih 
      have h3 : f ((↑(n : ℕ) * (2 : ℝ) - 1 : ℝ) + 1 ) = 1 := by 
        rw [h ((↑n * (2 : ℝ) - 1 : ℝ))]
        rw [h2]
        have h4 : Real.sqrt ( (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ 2 ) = 1 / 2 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h4]
        all_goals norm_num 
      have h5 : f (( (↑(n : ℕ) * (2 : ℝ) - 1 : ℝ) + 1 ) + 1 ) = 1 / 2 := by 
        rw [h (( (↑n * (2 : ℝ) - 1 : ℝ) + 1 ) ) ]
        rw [h3]
        have h6 : Real.sqrt ( (1 : ℝ) - (1 : ℝ) ^ 2 ) = (0 : ℝ) := by
          rw [Real.sqrt_eq_zero'] 
          norm_num
        rw [h6]
        all_goals norm_num 
      have h7 : (( (↑(n : ℕ) * (2 : ℝ) - 1 : ℝ) + 1 ) + 1 ) = (↑(n + 1 : ℕ) * (2 : ℝ) - 1 : ℝ) := by 
        simp at *
        all_goals ring_nf 
      rw [h7] at h5 
      linarith [h5]
  have h2 : (2007 : ℝ ) = (↑(1004 : ℕ ) * (2 : ℝ) - 1 : ℝ) := by 
    norm_num 
  rw [h2]
  apply h1 
  all_goals norm_num