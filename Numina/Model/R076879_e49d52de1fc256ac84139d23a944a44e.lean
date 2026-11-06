import Mathlib

theorem algebra_121915 {a b : ℕ → ℤ} (ha : ∀ n, ∑ i in Finset.range n, a i = 2 * a n - 1)
    (hb1 : b 1 = 3) (hbk : ∀ k, b (k + 1) = a k + b k) :
    ∀ n, ∑ i in Finset.range n, b i = 2 ^ n + 2 * n - 1 := by
  intro n 
  have h0 := ha 0
  norm_num at h0
  all_goals
    omega