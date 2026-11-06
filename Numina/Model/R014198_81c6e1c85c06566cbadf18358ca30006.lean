import Mathlib

theorem number_theory_67320 (x y : ℤ) (h0 : 17 ∣ x ^ 2 - 2 * x * y + y ^ 2 - 5 * x + 7 * y)
    (h1 : 17 ∣ x ^ 2 - 3 * x * y + 2 * y ^ 2 + x - y) :
    17 ∣ x * y - 12 * x + 15 * y := by
  have h2 : (x ^ 2 - 2 * x * y + y ^ 2 - 5 * x + 7 * y) % 17 = 0 := by
    omega
  have h3 : (x ^ 2 - 3 * x * y + 2 * y ^ 2 + x - y) % 17 = 0 := by
    omega
  have h4 : (x * y - 12 * x + 15 * y) % 17 = 0 := by
    have h2' : x % 17 = 0 ∨ x % 17 = 1 ∨ x % 17 = 2 ∨ x % 17 = 3 ∨ x % 17 = 4 ∨ x % 17 = 5 ∨ x % 17 = 6 ∨ x % 17 = 7 ∨ x % 17 = 8 ∨ x % 17 = 9 ∨ x % 17 = 10 ∨ x % 17 = 11 ∨ x % 17 = 12 ∨ x % 17 = 13 ∨ x % 17 = 14 ∨ x % 17 = 15 ∨ x % 17 = 16 := by 
      omega
    have h3' : y % 17 = 0 ∨ y % 17 = 1 ∨ y % 17 = 2 ∨ y % 17 = 3 ∨ y % 17 = 4 ∨ y % 17 = 5 ∨ y % 17 = 6 ∨ y % 17 = 7 ∨ y % 17 = 8 ∨ y % 17 = 9 ∨ y % 17 = 10 ∨ y % 17 = 11 ∨ y % 17 = 12 ∨ y % 17 = 13 ∨ y % 17 = 14 ∨ y % 17 = 15 ∨ y % 17 = 16 := by
      omega
    rcases h2' with (h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' | h2' ) <;> rcases h3' with (h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' ) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, h2', h3'] at h2 h3 ⊢ <;> omega
  exact Int.dvd_of_emod_eq_zero h4