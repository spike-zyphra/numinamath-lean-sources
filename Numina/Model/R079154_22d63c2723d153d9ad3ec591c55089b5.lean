import Mathlib

theorem number_theory_305553 (a b c : ℕ) (ha : a = 1993) (hb : b = 199) (hc : c = 18) :
    ¬∃ x y z, x + y + z = a + b + c ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x = a + b + c - z ∧ y = a + b + c - x ∧ z = a + b + c - y := by
  intro h
  rcases h with ⟨x, y, z, h1, h2, h3, h4, h5, h6, h7⟩
  norm_num [ha, hb, hc] at h1 h5 h6 h7
  omega