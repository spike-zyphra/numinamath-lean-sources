import Mathlib

theorem algebra_217027 (a b c d e f : ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
    (hd : d < 10) (he : e < 10) (hf : f < 10) (h1 : a = b + 1) (h2 : b = c + 2)
    (h3 : (100 * a + 10 * b + c) * 3 + 4 = (100 * d + 10 * e + f)) :
    100 * d + 10 * e + f = 964 := by
  have ha' : a = c + 3 := by 
    linarith [h1, h2]
  have eq1 : (100 * a + 10 * b + c) = 111 * c + 320 := by
    rw [ha', h2]
    omega 
  rw [eq1] at h3
  omega