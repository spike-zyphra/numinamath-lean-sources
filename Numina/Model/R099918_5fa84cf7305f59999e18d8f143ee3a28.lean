import Mathlib

theorem number_theory_324849 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x < 10) (hyz : y < 10) (hzx : z < 10) (h : (100 * x + 10 * y + z) ^ 2 = (x + y + z) ^ 5) :
    x ^ 2 + y ^ 2 + z ^ 2 = 29 := by
  have h1 : x ≤ 9 := by linarith
  have h2 : y ≤ 9 := by linarith
  have h3 : z ≤ 9 := by linarith
  interval_cases x <;> interval_cases y <;> interval_cases z
  <;> norm_num at h <;> norm_num at *
  <;> all_goals { trivial }