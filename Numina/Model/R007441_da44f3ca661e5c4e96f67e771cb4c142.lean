import Mathlib

open Int

-- Theorem: For any integer n, 6 divides n³ - 7n
theorem number_theory_607371 (n : ℤ) : 6 ∣ n^3 - 7 * n := by
  have h1 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
    omega

  rcases h1 with (h | h | h | h | h | h)
  · -- Case n ≡ 0 (mod 6)
    have h2 : (n ^ 3 - 7 * n) % 6 = 0 := by
      simp [pow_succ, Int.sub_emod, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Case n ≡ 1 (mod 6)
    have h2 : (n ^ 3 - 7 * n) % 6 = 0 := by
      simp [pow_succ, Int.sub_emod, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Case n ≡ 2 (mod 6)
    have h2 : (n ^ 3 - 7 * n) % 6 = 0 := by
      simp [pow_succ, Int.sub_emod, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Case n ≡ 3 (mod 6)
    have h2 : (n ^ 3 - 7 * n) % 6 = 0 := by
      simp [pow_succ, Int.sub_emod, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Case n ≡ 4 (mod 6)
    have h2 : (n ^ 3 - 7 * n) % 6 = 0 := by
      simp [pow_succ, Int.sub_emod, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Case n ≡ 5 (mod 6)
    have h2 : (n ^ 3 - 7 * n) % 6 = 0 := by
      simp [pow_succ, Int.sub_emod, Int.mul_emod, h, Int.add_emod, Int.sub_emod]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h2