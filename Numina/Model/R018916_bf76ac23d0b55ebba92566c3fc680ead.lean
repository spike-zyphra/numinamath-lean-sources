import Mathlib

theorem algebra_157113 (m : ℤ) (x : ℤ) (h : x = 5 * m + 4) :
    ¬ 5 ∣ (x ^ 2 + 1) := by
  rw [h]
  intro h1
  have h2 : 5 ∣ (5 * m + 4) ^ 2 + 1 := h1
  have h3 : (5 * m + 4) ^ 2 + 1 = 25 * m ^ 2 + 40 * m + 17 := by 
    ring
  rw [h3] at h2
  have h4 : (25 * m ^ 2 + 40 * m + 17) % 5 = 2 := by
    have h5 : (25 * m ^ 2) % 5 = 0 := by
      have h6 : 5 ∣ 25 * m ^ 2 := by
        omega
      omega
    have h7 : (40 * m) % 5 = 0 := by
      have h8 : 5 ∣ 40 * m := by
        omega
      omega
    have h8 : (17) % 5 = 2 := by
      omega
    simp [Int.add_emod, Int.mul_emod, h5, h7, h8]
  have h5 : (25 * m ^ 2 + 40 * m + 17) % 5 = 0 := by 
    omega
  omega