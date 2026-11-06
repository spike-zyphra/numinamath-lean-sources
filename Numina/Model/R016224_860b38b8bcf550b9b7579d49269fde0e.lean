import Mathlib

theorem number_theory_249478 {a b c d : ℤ} (h : a * d - b * c = 1) :
    IsCoprime (a ^ 2 + b ^ 2) (a * c + b * d) := by
  show IsCoprime (a ^ 2 + b ^ 2) (a * c + b * d)
  use c ^ 2 + d ^ 2
  use - (a * c + b * d)
  have h2 : (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) - (a * c + b * d) * (a * c + b * d) = 1 := by
    have h3 : (a * d - b * c) = 1 := h
    -- identity (a²+b²)(c²+d²) - (ac+bd)² = (ad-bc)²
    -- Expanding, we have:
    -- (a² + b²)(c² + d²) - (ac + bd)^2 = (ad - bc)^2
    -- a²d² + a²d² - 2abcd = 1
    have h4 : (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) - (a * c + b * d) * (a * c + b * d) = (a * d - b * c) ^ 2 := by
      ring
    rw [h4]
    rw [show (a * d - b * c) ^ 2 = 1 by rw [h3]; all_goals norm_num]
    all_goals norm_num
  linarith