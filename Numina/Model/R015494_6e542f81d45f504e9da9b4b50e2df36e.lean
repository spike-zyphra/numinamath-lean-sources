import Mathlib

theorem algebra_79927 (m n : ℝ) (hm : m > 0) (hn : n > 0)
    (h : ∃ x : ℝ, x^4 + 2 * x^2 + m * x + n = 0) (h' : ∀ m' n' : ℝ,
    m' > 0 → n' > 0 → (∃ x : ℝ, x^4 + 2 * x^2 + m' * x + n' = 0) →
    m ≤ m' ∧ n = n') (h'' : (1 : ℝ)^4 + 2 * (1 : ℝ)^2 + m * (1 : ℝ) + n = 99) :
    n = 56 := by

  have h_eq1 : m + n = 96 := by 
    nlinarith
  
  have h1 := h' 40 56 (by norm_num) (by norm_num) (by
    use -2
    norm_num
  )
  
  have h_eq2 : m ≤ (40 : ℝ) := by
    linarith [h1.1]
  
  have h_eq8 : n = 56 := by
    nlinarith [h_eq1, h_eq2]

  exact h_eq8