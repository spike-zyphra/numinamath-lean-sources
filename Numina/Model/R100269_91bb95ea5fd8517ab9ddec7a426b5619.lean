import Mathlib

theorem algebra_277568 (p q r s t u v w : ℕ) (h₀ : 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧ 0 < t ∧ 0 < u ∧ 0 < v ∧ 0 < w)
    (h₁ : p + q + r + s = 35) (h₂ : q + r + s + t = 35) (h₃ : r + s + t + u = 35)
    (h₄ : s + t + u + v = 35) (h₅ : t + u + v + w = 35) (h₆ : q + v = 14) :
    p ≤ 20 := by
  have h7 : p = t := by
    omega

  have h8 : q = u := by 
    omega
  have h9 : r = v := by
    omega

  have h10 : s = w := by
    omega

  have h11 : p + s = 21 := by
    have h7' : q + r = 14 := by 
      linarith [h₆, h9]
    omega

  omega