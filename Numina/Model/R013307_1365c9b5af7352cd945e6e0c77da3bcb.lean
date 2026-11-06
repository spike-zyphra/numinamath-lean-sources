import Mathlib

theorem algebra_203536 {x : ℕ → ℝ} (a b : ℝ) (h : x 1 = a) (h' : x 2 = b)
    (h'' : ∀ n ≥ 2, x (n + 1) = x n - x (n - 1)) :
    x 100 = -a ∧ ∑ i in Finset.range 100, x (i + 1) = 2 * b - a := by
  have h1 : x 100 = -a := by 
    set_option maxRecDepth 10000 in
    norm_num [h, h', h''] at *
  have h2 : ∑ i in Finset.range 100, x (i + 1) = 2 * b - a := by 
    set_option maxRecDepth 10000 in
    norm_num [Finset.sum_range_succ, h, h', h''] at *
    <;> linarith
  constructor
  · exact h1
  · exact h2