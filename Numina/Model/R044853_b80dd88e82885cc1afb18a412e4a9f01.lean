import Mathlib

theorem number_theory_166838 (a : ℕ → ℤ) (ha1 : a 1 = 1000000)
    (han : ∀ n, a (n + 1) = n * ⌊(a n : ℝ) / n⌋ + n) :
    ∃ d, {x | ∃ n, x = a n ∧ x = a 1 + d * (n - 1)}.Infinite := by 
  have h1 := han 0
  simp at h1 
  exfalso 
  linarith [ha1, h1]