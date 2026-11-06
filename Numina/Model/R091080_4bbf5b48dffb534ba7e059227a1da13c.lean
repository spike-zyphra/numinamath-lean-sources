import Mathlib

theorem algebra_244087 (p q r s k : ℤ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0 ∧ s > 0)
    (h1 : p + 2 * q + 3 * r + 4 * s = k) (h2 : 4 * p = 3 * q) (h3 : 3 * q = 2 * r)
    (h4 : 2 * r = s) :
    k ≥ 77 := by 
  rcases hpqr with ⟨hp, hq, hr, hs⟩
  omega