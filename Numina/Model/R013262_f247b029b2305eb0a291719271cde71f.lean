import Mathlib

theorem algebra_604060 (p : ℤ) (x : ℤ) :
    x^2 - 2 * x - (10 * p^2 + 10 * p + 2) ≠ 0 := by

  by_contra h
  have h1 : x^2 - 2 * x = 10 * p^2 + 10 * p + 2 := by linarith
  have h3 : (x ^ 2 - 2 * x) % 5 = 2 := by
    have h4 : x ^ 2 - 2 * x = 10 * p^2 + 10 * p + 2 := by linarith
    have h5 : (x ^ 2 - 2 * x) % 5 = (10 * p^2 + 10 * p + 2) % 5 := by rw [h4]
    simp [Int.add_emod, Int.mul_emod, Int.sub_emod] at h5 ⊢
    <;> omega
  have h4 : (x ^ 2 - 2 * x) % 5 = 0 ∨ (x ^ 2 - 2 * x) % 5 = 3 ∨ (x ^ 2 - 2 * x) % 5 = 4 := by
    have h5 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5) <;> simp [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, h5]
  omega