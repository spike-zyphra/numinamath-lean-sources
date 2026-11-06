import Mathlib

theorem number_theory_6126 (k : ℤ) : 3 ∣ 4 * k * (2 * k + 1) * (k + 1) := by
  have h1 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    omega
  rcases h1 with (h | h | h)
  · -- case k % 3 = 0
    have h2 : k % 3 = 0 := h
    have h3 : (4 * k * (2 * k + 1) * (k + 1)) % 3 = 0 := by
      simp [Int.mul_emod, Int.add_emod, h2]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h3
  · -- case k % 3 = 1
    have h2 : k % 3 = 1 := h
    have h3 : (4 * k * (2 * k + 1) * (k + 1)) % 3 = 0 := by
      simp [Int.mul_emod, Int.add_emod, h2]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h3
  · -- case k % 3 = 2
    have h2 : k % 3 = 2 := h
    have h3 : (4 * k * (2 * k + 1) * (k + 1)) % 3 = 0 := by
      simp [Int.mul_emod, Int.add_emod, h2]
      <;> omega
    exact Int.dvd_of_emod_eq_zero h3