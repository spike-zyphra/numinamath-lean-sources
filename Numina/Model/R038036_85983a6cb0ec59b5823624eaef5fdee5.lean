import Mathlib

theorem inequalities_165639 (a b c x y z k : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k)
    (h : a + x = k) (h' : b + y = k) (h'' : c + z = k) :
    a * y + b * z + c * x < k ^ 2 := by 
  have hx_eq : x = k - a := by linarith 
  have hy_eq : y = k - b := by linarith 
  have hz_eq : z = k - c := by linarith
  have h1 : 0 < k - a := by 
    nlinarith [h, hx]
  have h2 : 0 < k - b := by 
    nlinarith [h', hy]
  have h3 : 0 < k - c := by 
    nlinarith [h'', hz]
  rw [hx_eq, hy_eq, hz_eq]
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
    mul_pos (show 0 < k - a by nlinarith [h, hx]) 
    (show 0 < k - b by nlinarith [h', hy]), 
    mul_pos (show 0 < k - b by nlinarith [h', hy]) 
    (show 0 < k - c by nlinarith [h'', hz]), 
    mul_pos (show 0 < k - a by nlinarith [h, hx]) 
    (show 0 < k - c by nlinarith [h'', hz]), 
    mul_pos ha (show 0 < k - a by nlinarith [h, hx]), 
    mul_pos hb (show 0 < k - b by nlinarith [h', hy]), 
    mul_pos hc (show 0 < k - c by nlinarith [h'', hz]), 
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
    sq_nonneg (k - a - b), sq_nonneg (k - b - c), sq_nonneg (k - c - a)
  ]