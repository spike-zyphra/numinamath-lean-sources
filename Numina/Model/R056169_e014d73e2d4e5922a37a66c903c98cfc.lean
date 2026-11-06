import Mathlib

theorem algebra_199725 {a p n s : ℝ} (ha : 0 < a) (hp : 0 < p) (hn : 0 < n)
    (hs : 0 < s) (h : (1 - n / 1000) * p * s = a * x) (h' : (1 - n / 1000) * p * s = 1.5 * a * x)
    (hx : 0 < x) : (2.5 + p) * 1000 / (2000 - n) = x := by 
  have eq1 : a * x = 1.5 * a * x := by 
    nlinarith 
  have eq2 : a * x = 0 := by
    nlinarith [eq1, ha]
  have hx0 : x = 0 := by
    apply (mul_eq_zero.mp eq2).resolve_left 
    linarith 
  linarith [hx0, hx]