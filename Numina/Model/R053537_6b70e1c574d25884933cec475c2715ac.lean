import Mathlib

theorem number_theory_310590 (a b c : ℕ) (ha : a = 51) (hb : b = 49) (hc : c = 5)
    (h1 : ∃ x y z, x + y = z ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = a + b + c)
    (h2 : ∃ x y, x > 0 ∧ y > 0 ∧ x + y = a + b + c ∧ Even (x + y)) :
    ¬∃ x y, x > 0 ∧ y > 0 ∧ x + y = a + b + c ∧ x + y + z = 105 := by
  rintro ⟨x, y, hx, hy, hsum, hsum2⟩
  rcases h1 with ⟨x1, y1, z1, h12, hx1, hy1, hz1, hn1⟩
  omega