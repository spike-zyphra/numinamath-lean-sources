import Mathlib

theorem algebra_327233 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h1 : a 1 = 2012) (h2 : ∃ m n, a 2 = m ∧ a 3 = n)
    (h3 : ∃ r, ∀ n, n * a n - n ^ 2 = r ^ n) (h4 : r ≤ 10) :
    ∀ n, a n = (2011 * 6 ^ (n - 1)) / n + n := by 
  rcases h3 with ⟨r, hr⟩ 
  have h0 := hr 0
  norm_num at h0 
  all_goals 
    linarith