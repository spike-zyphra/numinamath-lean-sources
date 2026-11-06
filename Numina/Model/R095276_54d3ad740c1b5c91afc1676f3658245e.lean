import Mathlib

theorem number_theory_296409
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : ∃ q : ℚ, (Real.sqrt 3 * a + b) / (Real.sqrt 3 * b + c) = q) :
    ∃ m : ℤ, (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) = m := by 
  refine' ⟨(a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c), by omega⟩