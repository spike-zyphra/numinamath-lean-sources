import Mathlib

theorem number_theory_214141 (x y : ℤ) : ¬(5*x^2-4*y^2=2017) := by
  intro h
  have h1 : (5 * x ^ 2 - 4 * y ^ 2 : ℤ) = 2017 := by
    linarith
  have h2 : (5 * x ^ 2 - 4 * y ^ 2 : ℤ) % 5 = 2017 % 5 := by
    rw [h1]
  norm_num at h2
  have h3 : (y ^ 2) % 5 = 0 ∨ (y ^ 2) % 5 = 1 ∨ (y ^ 2) % 5 = 4 := by
    have h4 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    rcases h4 with (h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
  have h4 : (5 * x ^ 2 - 4 * y ^ 2 : ℤ) % 5 = (- (4 * y ^ 2) ) % 5 := by
    omega
  have h5 : (y ^ 2) % 5 = 2 := by
    omega
  omega