import Mathlib

theorem number_theory_2505 (n : ℤ) :
    Odd ((n + 1)^3 - n^3) := by
  have h1 : (n + 1)^3 - n^3 = 3 * n^2 + 3 * n + 1 := by
    ring_nf
  rw [h1]
  have h2 : (3 * n^2 + 3 * n) % 2 = 0 := by
    have h4 : (n % 2 = 0) ∨ (n % 2 = 1) := by
      omega
    rcases h4 with (h | h)
    · -- Case where n % 2 = 0
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
      <;> omega
    · -- Case where n % 2 = 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h]
      <;> omega
  have h3 : (3 * n^2 + 3 * n) = 2 * ((3 * n^2 + 3 * n) / 2) := by
    omega
  rw [h3]
  simp [Int.odd_iff]
  <;> omega