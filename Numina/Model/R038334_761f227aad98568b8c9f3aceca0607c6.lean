import Mathlib

theorem algebra_306385 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hper : ∀ x, f (x + 5) = f x)
    (hf : f 1 = 8) : f 2010 - f 2009 = 8 := by
  have h0 : f 0 = 0 := by
    have h1 := hodd 0
    norm_num at h1 
    linarith
  have h4_eq_neg8 : f 4 = -8 := by
    have eq1 : f 4 = f (-1) := by 
      have eq2 : f (-1 + 5) = f (-1) := by 
        specialize hper (-1)
        simpa using hper 
      have eq3 : -1 + (5 : ℝ) = (4 : ℝ) := by norm_num
      rw [eq3] at eq2 
      linarith 
    have eq2 : f (-1) = -f 1 := by
      specialize hodd 1 
      linarith 
    rw [eq1] 
    rw [eq2, hf] 
    all_goals linarith
  have h1 : f 2010 = f 0 := by
    have h2 : ∀ (n : ℕ), f ((↑n : ℝ) * (5 : ℝ)) = f 0 := by
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih =>
        have eq3 : f ( (↑n * (5 : ℝ) + (5 : ℝ) ) ) = f (↑n * (5 : ℝ) ) := by 
          specialize hper (↑n * (5 : ℝ) )
          simpa using hper
        have eq1 : f ( (↑(n + 1 : ℕ) : ℝ) * (5 : ℝ) ) = f (↑n * (5 : ℝ) + 5) := by
          simp [mul_add, add_mul, mul_add, mul_one] at *
          <;> ring_nf
        have eq2 : f (↑n * (5 : ℝ) ) = f 0 := ih
        rw [eq1] 
        linarith [eq3, eq2]
    specialize h2 402 
    norm_num at h2 ⊢ 
    linarith
  have h2009 : f 2009 = f 4 := by
    have h3 : ∀ (n : ℕ), f (4 + (↑n : ℝ) * (5 : ℝ)) = f 4 := by 
      intro n 
      induction n with
      | zero => 
        simp 
      | succ n ih => 
        have eq3 : f ( (4 + (↑(n + 1 : ℕ) : ℝ) * (5 : ℝ) ) ) = f ( 4 + (↑n * (5 : ℝ) ) + 5 ) := by 
          simp [mul_add, add_mul, mul_add, mul_one] at *
          <;> ring_nf 
        have eq4 : f (4 + (↑n * (5 : ℝ) ) + (5 : ℝ) ) = f (4 + (↑n * (5 : ℝ) ) ) := by 
          have eq5 : f ( (4 + (↑n * (5 : ℝ) ) ) + (5 : ℝ) ) = f ( (4 + (↑n * (5 : ℝ) ) ) ) := by 
            specialize hper (4 + (↑n * (5 : ℝ) ) ) 
            simpa using hper 
          ring_nf at eq5 ⊢ 
          all_goals linarith 
        have eq5 : f (4 + (↑n * (5 : ℝ) ) ) = f 4 := ih 
        rw [eq3] 
        linarith [eq4, eq5]
    specialize h3 401 
    norm_num at h3 ⊢ 
    linarith
  have h5 : f 2009 = -8 := by
    linarith [h2009, h4_eq_neg8]
  have eq6 : f 2010 = 0 := by 
    linarith [h1, h0]
  linarith [eq6, h5]