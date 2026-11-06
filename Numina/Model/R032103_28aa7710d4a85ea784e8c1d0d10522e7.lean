import Mathlib

theorem number_theory_6827 (a b : ℤ) (_ : 0 < a) (h₁ : 0 < b)
    (h₂ : Int.gcd a b = 1) :
    ∃ x y, a * x + b * y = 1 := by 
  use Int.gcdA a b, Int.gcdB a b
  have h3 : a * Int.gcdA a b + b * Int.gcdB a b = Int.gcd a b := by 
    rw [Int.gcd_eq_gcd_ab]
  rw [h3, h₂]
  all_goals omega