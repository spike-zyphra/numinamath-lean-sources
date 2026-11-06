import Mathlib

theorem number_theory_240228 (a b : ℤ) (h₀ : Odd (a + b)) :
    Even (a * b) := by
  obtain ⟨k, hk⟩ := h₀
  have h1 : a % 2 = 0 ∨ b % 2 = 0 := by
    omega
  rcases h1 with (h | h)
  · -- Assume a % 2 = 0, prove Even (a * b)
    have : (a * b) % 2 = 0 := by
      have ha : a % 2 = 0 := h
      simp [Int.mul_emod, ha]
      all_goals omega
    exact ⟨(a * b) / 2, by omega⟩
  · -- Assume b % 2 = 0, prove Even (a * b)
    have : (a * b) % 2 = 0 := by
      have hb : b % 2 = 0 := h
      simp [Int.mul_emod, hb]
      all_goals omega
    exact ⟨(a * b) / 2, by omega⟩