import Mathlib

theorem algebra_16399 (c o u n t s : ℕ) (hc : c > 0 ∧ c < 10) (ho : o > 0 ∧ o < 10)
    (hu : u > 0 ∧ u < 10) (hn : n > 0 ∧ n < 10) (ht : t > 0 ∧ t < 10) (hs : s > 0 ∧ s < 10)
    (h1 : c + o = u) (h2 : u + n = t) (h3 : t + c = s) (h4 : o + n + s = 12) : t = 6 := by
  have h5 : u = c + o := by 
    linarith
  have h6 : t = c + o + n := by 
    linarith [h2, h5]
  have h7 : s = 2 * c + o + n := by 
    rw [h6] at h3
    omega
  have h8 : 2 * c + 2 * o + 2 * n = 12 := by 
    linarith [h4, h7]
  have h9 : c + o + n = 6 := by 
    omega
  linarith [h6, h9]