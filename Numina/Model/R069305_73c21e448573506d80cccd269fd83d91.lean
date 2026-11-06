import Mathlib

theorem inequalities_46092 (f : ℝ → ℝ) (g : ℝ → ℝ)
    (h₀ : f 1 = 1) (h₁ : ∀ x, f (x + 5) ≥ f x + 5) (h₂ : ∀ x, f (x + 1) ≤ f x + 1)
    (h₃ : g = fun x => f x + 1 - x) :
    g 2016 = 1 := by
  have lower_bound : f 2016 ≥ 2016 := by
    have h4 : ∀ n : ℕ, f (1 + (n : ℝ) * 5) ≥ f 1 + (n : ℝ) * 5 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have eq1 : (1 + ((n + 1 : ℕ) : ℝ) * 5) = (1 + ((n : ℕ) : ℝ) * 5) + 5 := by
          simp [mul_add, add_mul]
          <;> ring_nf <;> norm_num
          <;> ring
        rw [eq1]
        have h5 := h₁ (1 + ((n : ℕ) : ℝ) * 5)
        linarith [ih, h5]
    have h5 : f 2016 ≥ 2016 := by
      specialize h4 403
      norm_num at h4 ⊢
      linarith [h₀]
    linarith
  have upper_bound : f 2016 ≤ 2016 := by
    have h6 : ∀ n : ℕ, f (1 + (n : ℝ)) ≤ f 1 + (n : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have eq2 : (1 + ((n + 1 : ℕ) : ℝ)) = (1 + ((n : ℕ) : ℝ)) + 1 := by
          simp [mul_add, add_mul]
          <;> ring_nf <;> norm_num
          <;> ring
        rw [eq2]
        have h₃' := h₂ (1 + ((n : ℕ) : ℝ))
        linarith [ih, h₃']
    have h7 : f 2016 ≤ 2016 := by
      specialize h6 2015
      norm_num at h6 ⊢
      linarith [h₀]
    linarith
  have hf2016 : f 2016 = 2016 := by 
    linarith [lower_bound, upper_bound]
  rw [h₃]
  simp [hf2016]
  all_goals norm_num