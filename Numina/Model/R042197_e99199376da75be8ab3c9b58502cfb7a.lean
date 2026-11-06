import Mathlib

theorem number_theory_313502 (a : ℕ → ℤ)
    (h₀ : a 1 = 2008)
    (h₁ : ∀ n, a (n + 1) = n * ⌊(a n / n : ℝ)⌋ + n) :
    ∃ d, {x | ∃ n, x = a n ∧ x = a 1 + d * (n - 1)}.Infinite ∧
    ∃ r, {x | ∃ n, x = a n ∧ x = a 1 * r ^ (n - 1)}.Infinite := by 
  have h2 : a 1 = 0 := by 
    specialize h₁ 0 
    norm_num at h₁ ⊢ 
    all_goals linarith 
  linarith [h₀, h2]