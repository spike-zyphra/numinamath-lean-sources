import Mathlib

theorem algebra_3546 (a b c d e : ℤ) (ha : a ≤ b) (hb : b ≤ c) (hc : c ≤ d)
    (hd : d ≤ e) (h : (a + b + c + d + e) / 5 = a) (h' : (c + d) / 2 = b) (h'' : d = c) :
    e - a ≤ 7 := by

  have h3 : b = c := by
    rw [show d = c by linarith [h'']] at h'
    have h4 : (c + c) / 2 = b := by 
      omega
    -- Simplify h4: (c + c) / 2 = b
    have h5 : (2 * c) / 2 = b := by
      omega
    have h6 : c = b := by 
      omega
    linarith

  have h4 : c = d := by 
    linarith [h'']

  have h5 : b = d := by 
    linarith [h3, h4]

  have h1 : 5 * a ≤ a + b + c + d + e := by 
    omega

  have h2 : a + b + c + d + e < 5 * a + 5 := by 
    omega

  omega