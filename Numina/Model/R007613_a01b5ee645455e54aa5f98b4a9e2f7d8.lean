import Mathlib

theorem algebra_167474 {k : ℕ} (hk : 0 < k) (h : 2012^2 + 2010 * 2011 * 2013 * 2014 = k^2) :
    k = 4048142 := by
  have h1 : k^2 = 4048142^2 := by
    nlinarith
  have h2 : k = 4048142 := by
    nlinarith [h1, hk]
  exact h2