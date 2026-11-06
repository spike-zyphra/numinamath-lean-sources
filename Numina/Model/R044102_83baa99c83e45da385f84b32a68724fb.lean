import Mathlib

theorem number_theory_217292 : ¬ ∃ x y : ℤ, 3*x^4+2013=25*y^2-24*x^2 := by
  intro h
  rcases h with ⟨x, y, h_eq⟩
  have eq1 : 3 * x^4 + 24 * x^2 + 2013 = 25 * y^2 := by
    nlinarith
  have eq2 : (3 * x^4 + 24 * x^2 + 2013) % 25 = 0 := by
    omega
  have h1 : x % 25 = 0 ∨ x % 25 = 1 ∨ x % 25 = 2 ∨ x % 25 = 3 ∨ x % 25 = 4 ∨ x % 25 = 5 ∨ x % 25 = 6 ∨ x % 25 = 7 ∨ x % 25 = 8 ∨ x % 25 = 9 ∨ x % 25 = 10 ∨ x % 25 = 11 ∨ x % 25 = 12 ∨ x % 25 = 13 ∨ x % 25 = 14 ∨ x % 25 = 15 ∨ x % 25 = 16 ∨ x % 25 = 17 ∨ x % 25 = 18 ∨ x % 25 = 19 ∨ x % 25 = 20 ∨ x % 25 = 21 ∨ x % 25 = 22 ∨ x % 25 = 23 ∨ x % 25 = 24 := by 
    omega
  rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, pow_three, pow_succ', Int.add_emod, Int.mul_emod, Int.sub_emod, Int.mul_emod, pow_mul, pow_add] at eq2 <;> omega