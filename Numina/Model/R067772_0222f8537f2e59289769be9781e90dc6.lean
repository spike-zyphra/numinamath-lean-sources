import Mathlib

theorem algebra_298119 (a : ℕ → ℝ) (h₀ : a 4 = 1) (h₁ : a 11 = 9)
    (h₂ : ∀ n, a n + a (n + 1) + a (n + 2) = 15) :
    a 2016 = 5 := by

  have eq1 : ∀ k, a (k + 3) = a k := by
    intro k
    have T₁ := h₂ k
    have T₂ := h₂ (k + 1)
    simp at T₁ T₂
    linarith

  have a4 : a 5 = 9 := by
    have eq5 := eq1 5
    have eq8 := eq1 8
    norm_num at eq5 eq8
    have h8 : a 8 = 9 := by
      linarith [h₁, eq8]
    linarith [h8, eq5]

  have a6 : a 6 = 5 := by
    have T₁ := h₂ 4
    norm_num [h₀, a4] at T₁
    nlinarith
  
  have a1 : a 1 = 1 := by
    have eq23 := eq1 1
    norm_num [h₀] at eq23
    linarith

  have a2 : a 2 = 9 := by 
    have eq23 := eq1 2
    norm_num [a4] at eq23 
    linarith

  have a3 : a 3 = 5 := by
    have eq5 := eq1 3
    norm_num [a6] at eq5 
    linarith
  
  have a0 : a 0 = 5 := by
    have eq0 := eq1 0
    norm_num [a3] at eq0 
    linarith
  
  have h₃ : ∀ k : ℕ, a (3 * k) = 5 := by
    intro k
    induction k with
    | zero =>
      simpa using a0
    | succ k ihk =>
      have eq12 := eq1 (3 * k)
      simp [show 3 * k + 3 = 3 * (k + 1) by ring] at eq12 ⊢
      rw [eq12]
      linarith [ihk]

  have : 2016 = 3 * 672 := by norm_num

  rw [this]
  specialize h₃ 672
  linarith [h₃]