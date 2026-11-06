import Mathlib

theorem algebra_190385 (a : ℕ → ℕ) (h₀ : ∑ i ∈ Finset.range 10, a i = 150)
    (h₁ : ∀ i ∈ Finset.range 9, a i < a (i + 1)) (h₂ : a 0 ≥ (1 / 2 : ℚ) * a 9) :
    a 5 = 16 := by
  have h3 : a 0 < a 1 := by 
    specialize h₁ 0 (by simp)
    simpa using h₁
  have h4 : a 1 < a 2 := by
    specialize h₁ 1 (by simp)
    simpa using h₁
  have h5 : a 2 < a 3 := by
    specialize h₁ 2 (by simp)
    simpa using h₁
  have h6 : a 3 < a 4 := by 
    specialize h₁ 3 (by simp)
    simpa using h₁
  have h7 : a 4 < a 5 := by
    specialize h₁ 4 (by simp)
    simpa using h₁
  have h8 : a 5 < a 6 := by 
    specialize h₁ 5 (by simp)
    simpa using h₁
  have h9 : a 6 < a 7 := by
    specialize h₁ 6 (by simp)
    simpa using h₁
  have h10 : a 7 < a 8 := by 
    specialize h₁ 7 (by simp)
    simpa using h₁
  have h11 : a 8 < a 9 := by 
    specialize h₁ 8 (by simp)
    simpa using h₁
  have h12 : (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9) = 150 := by 
    norm_num [Finset.sum_range_succ] at h₀ ⊢
    exact h₀
  have h13 : (a 0 : ℚ) ≥ (1 / 2 : ℚ) * (a 9 : ℚ) := by 
    simpa using h₂
  have h14 : (2 * (a 0 : ℚ) ≥ (a 9 : ℚ)) := by 
    nlinarith
  have h15 : 2 * a 0 ≥ a 9 := by 
    exact_mod_cast h14
  all_goals 
    omega