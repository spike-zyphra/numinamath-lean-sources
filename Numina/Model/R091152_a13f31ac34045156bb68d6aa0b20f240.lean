import Mathlib

theorem algebra_316172 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hsymm : ∀ x, f (1 / 2 - x) = f (1 / 2 + x)) :
    ∑ i ∈ Finset.range 2006, f (i + 1) = 0 := by 
  have h1 : f 0 = 0 := by
    specialize hodd 0
    norm_num at hodd 
    linarith
  have h2 : f 1 = 0 := by 
    have h3 : f (1 / 2 - (1 / 2 : ℝ)) = f (1 / 2 + (1 / 2 : ℝ)) := by
      apply hsymm
    norm_num at h3
    have h0 : f 0 = 0 := h1
    linarith [h0]
  have h3 : ∀ n : ℕ, f ((n + 1 : ℝ)) = - f ((n : ℝ)) := by
    intro n
    have h4 : f (-(n : ℝ)) = -f ((n : ℝ)) := by
      specialize hodd (n : ℝ)
      simpa using hodd
    have h5 : f (1 / 2 - ((n : ℝ) + 1 / 2)) = f (1 / 2 + ((n : ℝ) + 1 / 2)) := by
      apply hsymm
    have h6 : (1 / 2 - ((n : ℝ) + 1 / 2 : ℝ)) = -(n : ℝ) := by ring
    have h7 : (1 / 2 + ((n : ℝ) + 1 / 2 : ℝ)) = (n + 1 : ℝ) := by ring
    rw [h6] at h5 
    rw [h7] at h5 
    linarith [h4, h5]
  have h4' : ∀ n : ℕ, f ((n : ℝ) + 1) = 0 := by 
    intro n 
    induction n with 
    | zero =>
      norm_num [h2]
    | succ n ih =>
      have eq1 : f ((n + 1 + 1 : ℝ)) = - f ((n + 1 : ℝ)) := by 
        specialize h3 (n + 1)
        norm_num at h3 ⊢
        simpa using h3
      have eq2 : f ((n + 1 : ℝ)) = 0 := by 
        simpa using ih
      norm_num at eq1 ⊢
      rw [eq1]
      rw [eq2]
      all_goals norm_num
  simp [Finset.sum_eq_zero, h4']
  <;> norm_num
  <;> linarith