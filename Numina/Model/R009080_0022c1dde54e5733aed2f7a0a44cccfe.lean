import Mathlib

theorem algebra_14912 : IsGreatest {x : ℝ | 5 * (9 * x ^ 2 + 9 * x + 10) = x * (9 * x - 40)} (-10 / 9):= by
  constructor
  · -- Show that -10/9 is in the set
    norm_num
  · -- Show that any element x in the set is ≤ -10/9
    intro x hx
    have h : 5 * (9 * x ^ 2 + 9 * x + 10) = x * (9 * x - 40) := hx
    have h1 : 36 * x^2 + 85 * x + 50 = 0 := by
      nlinarith
    have h2 : (x + 10 / 9) * (x + 5 / 4) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where $x + 10/9 = 0$, so $x = -10/9$
      have h5 : x = -10 / 9 := by linarith
      linarith
    · -- Case where $x + 5/4 = 0$, so $x = -5/4$ which is less than $-10/9$
      have h5 : x = -5 / 4 := by linarith
      linarith