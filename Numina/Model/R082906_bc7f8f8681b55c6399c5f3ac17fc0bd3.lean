import Mathlib

theorem number_theory_188097 (a b c : ℕ) (ha : a = 19) (hb : b = 8) (hc : c = 9)
    (h1 : ∃ x y z, x + y + z = 33 ∧ a - x - y + z = 2 ∧ b - x + y - z = 12 ∧ c - y - z + x = 22) :
    x = 6 := by 
  rcases h1 with ⟨x, y, z, h2, h3, h4, h5⟩
  subst ha hb hc
  omega