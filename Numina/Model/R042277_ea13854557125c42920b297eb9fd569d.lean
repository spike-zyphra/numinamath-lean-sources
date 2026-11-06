import Mathlib

theorem algebra_194903 (a : ℕ) (ha : a^2 = 1000 * 1001 * 1002 * 1003 + 1) :
    a = 1003001 := by
  have h1 : a^2 = 1003001^2 := by
    nlinarith
  have h2 : a = 1003001 := by
    nlinarith [show a ≤ 1003001 by nlinarith [h1], show 1003001 ≤ a by nlinarith [h1]]
  exact h2