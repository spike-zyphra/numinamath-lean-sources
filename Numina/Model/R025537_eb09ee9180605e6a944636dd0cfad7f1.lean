import Mathlib

theorem number_theory_303901 {r : ℚ} : ∃ n m : ℤ, m ≠ 0 ∧ r = n / m := by
  use r.num
  use r.den
  constructor
  · -- Show that the denominator is non-zero 
    have h1 : r.den > 0 := by
      apply Rat.den_pos
    have h2 : (r.den : ℤ) ≠ 0 := by
      omega
    exact h2
  · -- Show that r = (r.num) / (r.den)
    field_simp