import Mathlib

theorem number_theory_249041 (x y : ℝ) (hx : x^2 - x + 1 = 5 * y) :
    ¬∃ m n : ℤ, x = m ∧ y = n := by
  rintro ⟨m, n, hx_eq, hy_eq⟩
  rw [hx_eq] at hx
  rw [hy_eq] at hx
  have h1 : (m : ℝ) ^ 2 - (m : ℝ) + 1 = 5 * (n : ℝ) := by
    exact_mod_cast hx
  have h2 : m^2 - m + 1 = 5 * n := by
    exact_mod_cast h1
  have h3 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
    omega
  rcases h3 with (h | h | h | h | h)
  · -- m % 5 = 0
    have h4 : m % 5 = 0 := h
    have h5 : (m ^ 2 - m + 1) % 5 = 1 := by
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h4]
    omega
  · -- m % 5 = 1
    have h4 : m % 5 = 1 := h
    have h5 : (m ^ 2 - m + 1) % 5 = 1 := by
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h4]
    omega
  · -- m % 5 = 2
    have h4 : m % 5 = 2 := h
    have h5 : (m ^ 2 - m + 1) % 5 = 3 := by
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h4]
    omega
  · -- m % 5 = 3
    have h4 : m % 5 = 3 := h
    have h5 : (m ^ 2 - m + 1) % 5 = 2 := by
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h4]
    omega
  · -- m % 5 = 4
    have h4 : m % 5 = 4 := h
    have h5 : (m ^ 2 - m + 1) % 5 = 3 := by
      simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h4]
    omega