import Mathlib

theorem algebra_93501 (a b c : ℝ) (ha : a = 4.4) (hb : b = 4.8) (hc : c = 5.0)
    (h : ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * 500 = y * 440 ∧ y * 500 = z * 480 ∧ z * 500 = x * 500) :
    x * 500 = 2500 := by 
  rcases h with ⟨x, y, z, hx, hy, hz, h1, h2, h3⟩
  nlinarith