import Mathlib

theorem number_theory_112113 (a : ℤ) (h : ¬ 5 ∣ a) : ¬ 5 ∣ 3 * a^4 + 1 := by
  have h1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- Case a % 5 = 1
    have h2 : (3 * a^4 + 1) % 5 = 4 := by
      have h3 : a % 5 = 1 := h1
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · -- Case a % 5 = 2
    have h2 : (3 * a^4 + 1) % 5 = 4 := by
      have h3 : a % 5 = 2 := h1
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · -- Case a % 5 = 3
    have h2 : (3 * a^4 + 1) % 5 = 4 := by
      have h3 : a % 5 = 3 := h1
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · -- Case a % 5 = 4
    have h2 : (3 * a^4 + 1) % 5 = 4 := by
      have h3 : a % 5 = 4 := h1
      simp [h3, pow_succ, Int.add_emod, Int.mul_emod]
    omega