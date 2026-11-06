import Mathlib

theorem other_80080 (a b : ℕ → ℝ) (q : ℝ) (hq : q > 1)
    (h : ∃ d, ∀ n, a n = a 0 + d * n) (h' : ∀ n, b n = b 0 * q ^ n) :
    q ∈ Set.Ioi 1 := by 
  exact hq