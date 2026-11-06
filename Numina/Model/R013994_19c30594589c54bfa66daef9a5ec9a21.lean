import Mathlib

theorem algebra_161645 {a b c d x : ℝ} (ha : a ≠ c) (h : a + d = 2015) (h' : b + c = 2015)
    (h'' : (x - a) * (x - b) = (x - c) * (x - d)) : x = 1007.5 := by
  have eq1 : d = 2015 - a := by linarith
  have eq2 : b = 2015 - c := by linarith
  rw [eq1, eq2] at h''
  have eq4 : 2 * (c - a) * x + 2015 * (a - c) = 0 := by
    nlinarith
    <;> ring_nf <;> nlinarith
  have h1 : c - a ≠ 0 := by
    intro h0
    apply ha
    linarith
  have eq6 : x = (2015 / 2 : ℝ) := by
    apply (mul_left_inj' (show c - a ≠ 0 by exact h1)).mp
    linarith
  rw [eq6]
  all_goals norm_num