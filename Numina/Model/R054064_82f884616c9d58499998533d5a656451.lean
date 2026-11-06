import Mathlib

theorem algebra_138740 {a b c d e f : ℝ} (ha : a = b - c + e) (hb : b = -e - c + a)
    (hc : c = -e - a + b) : a - b - c = a - b + e := by
  have he : e = 0 := by 
    linarith [ha, hb, hc]
  have h1 : b = a := by
    rw [he] at hb hc
    linarith [hb, hc]
  linarith [hc, h1, he]