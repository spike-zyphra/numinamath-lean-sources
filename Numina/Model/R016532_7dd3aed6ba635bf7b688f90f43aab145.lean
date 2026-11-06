import Mathlib

open scoped BigOperators

theorem algebra_292407
  (a : ℕ → ℝ)
  (h₀ : a 1 = 1)
  (h₁ : ∀ n ≥ 2, a n = a (n - 1) + 1 / a (n - 1)) :
  a 100 > 14 := by
  have h₂ : ∀ (n : ℕ), a (n + 1) > 0 := by 
    intro n
    induction n with 
    | zero => 
      rw [h₀]
      norm_num 
    | succ n ih => 
      have eq1 : (n + 1 + 1 : ℕ) ≥ 2 := by linarith 
      have h32 : a (n + 1 + 1) = a (n + 1) + 1 / a (n + 1) := by 
        specialize h₁ (n + 1 + 1) eq1 
        simpa using h₁ 
      have h4_eq3 : a (n + 1) > 0 := by simpa using ih 
      rw [h32] 
      positivity 
  have h₃ : ∀ (n : ℕ), (a (n + 1) ^ 2) ≥ (2 * ((↑(n + 1) : ℝ)) - 1) := by 
    intro n 
    induction n with 
    | zero => 
      rw [h₀]
      norm_num
      <;> linarith 
    | succ n ih => 
      have eq1 : (n + 1 + 1 : ℕ) ≥ 2 := by linarith 
      have h32 : a (n + 1 + 1) = a (n + 1) + 1 / a (n + 1) := by 
        specialize h₁ (n + 1 + 1) eq1 
        simpa using h₁ 
      have eq4 : a (n + 1) > 0 := by 
        specialize h₂ n 
        simpa using h₂ 
      have eq3' : a (n + 1 + 1) ^ 2 = (a (n + 1) ) ^ 2 + 2 + 1 / (a (n + 1) ^ 2) := by 
        rw [h32] 
        field_simp [show a (n + 1) ≠ 0 by linarith] 
        <;> ring_nf <;> field_simp [show a (n + 1) ≠ 0 by linarith]
      rw [eq3']
      rw [show (2 * ((↑(n + 1 + 1) : ℝ)) - 1) = (2 * ((↑(n + 1) ) : ℝ) - 1 + 2 : ℝ) by 
        simp at *
        <;> ring_nf <;> norm_num 
      ]
      have h5 : (a (n + 1) ) ^ 2 ≥ (2 * ((↑(n + 1) ) : ℝ) - 1 : ℝ) := by 
        simpa using ih 
      have h6 : (1 / (a (n + 1) ^ 2) ) > 0 := by 
        positivity 
      nlinarith 
      all_goals nlinarith
  
  have h400 : a 100 ^ 2 ≥ 199 := by 
    specialize h₃ 99 
    norm_num at h₃ ⊢ 
    linarith 
  have h5 : a 100 > 14 := by 
    have h60 : a 100 ^ 2 ≥ 199 := h400 
    have h70 : a 100 > 0 := by 
      specialize h₂ 99 
      norm_num at h₂ ⊢ 
      linarith 
    nlinarith 
  exact h5