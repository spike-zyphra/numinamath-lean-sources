import Mathlib

theorem number_theory_7769 (a b : ℤ) (d : ℤ) (h : d = a.gcd b) :
    ∃ x y, a * x + b * y = d := by
  rw [h]
  exact ⟨a.gcdA b, a.gcdB b, by rw [Int.gcd_eq_gcd_ab a b]⟩