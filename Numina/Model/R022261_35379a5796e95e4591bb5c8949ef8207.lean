import Mathlib

theorem algebra_130719 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h6 : (a 6 - 1)^3 + 2013 * (a 6 - 1)^3 = 1) (h2008 : (a 2008 - 1)^3 = 2013 * (a 2008 - 1)^3)
    (h2008' : 2013 * (a 2008 - 1)^3 = -1) :
    ∑ i in Finset.range 2013, a i = 2013 ∧ a 2008 * a 6 = -1 := by 
  have h2008_1 : (a 2008 - 1)^3 = 0 := by
    nlinarith
  rw [h2008_1] at h2008'
  all_goals nlinarith