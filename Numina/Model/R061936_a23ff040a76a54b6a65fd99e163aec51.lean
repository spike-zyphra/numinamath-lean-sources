import Mathlib

theorem number_theory_124509 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a + b + c = 2015) (h' : ∃ x y z, a = x + y + z ∧ b = y + z + x ∧ c = z + x + y) :
    max (max a b) c = 676 := by
  rcases h' with ⟨x, y, z, ha1, hb1, hc1⟩
  omega