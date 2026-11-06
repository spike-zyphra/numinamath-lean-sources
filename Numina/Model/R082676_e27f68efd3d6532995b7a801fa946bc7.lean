import Mathlib

theorem algebra_228715 (a b c d e f g : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) (h1 : a + b + c = 2) (h2 : b + c + d = 2)
    (h3 : c + d + e = 2) (h4 : d + e + f = 2) (h5 : e + f + g = 2) :
    a + b + c + d + e + f + g ≤ 6 := by 
  omega