import Mathlib

theorem number_theory_7150 (a b d : ℤ) (h : a.gcd b = d) :
    ∃ x y : ℤ, d = a * x + b * y := by 
  rw [show d = a.gcd b by rw [h]]
  exact ⟨a.gcdA b, a.gcdB b, by 
    rw [Int.gcd_eq_gcd_ab a b]
    all_goals ring
  ⟩