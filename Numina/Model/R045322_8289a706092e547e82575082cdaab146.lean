import Mathlib

theorem number_theory_218399 (n : ℤ) (h₀ : Odd n) : 24 ∣ n^3 - n := by
  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := h₀
    omega
  have h3 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have h1' : n % 2 = 1 := h1
    omega
  have h4 : (n ^ 3 : ℤ) % 8 = (n % 8) := by
    rcases h3 with (h | h | h | h)
    · simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  have h5 : (n ^ 3 : ℤ) % 3 = (n % 3) := by
    rcases h2 with (h6 | h6 | h6)
    · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h6, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  omega