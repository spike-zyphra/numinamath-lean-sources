import Mathlib

theorem number_theory_173827 (p : ℤ) :
    ¬∃ x : ℤ, x^2 - 2 * x - (10 * p^2 + 10 * p + 2) = 0 := by
  rintro ⟨x, hx⟩
  have h1 : x ^ 2 - 2 * x = 10 * p ^ 2 + 10 * p + 2 := by
    linarith
  have h2 : (x ^ 2 - 2 * x) % 10 = 2 := by
    omega
  have h3 : x % 10 = 0 ∨ x % 10 = 1 ∨ x % 10 = 2 ∨ x % 10 = 3 ∨ x % 10 = 4 ∨ x % 10 = 5 ∨ x % 10 = 6 ∨ x % 10 = 7 ∨ x % 10 = 8 ∨ x % 10 = 9 := by 
    omega
  rcases h3 with (h | h | h | h | h | h | h | h | h | h) <;> simp [h, 
    pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at h2