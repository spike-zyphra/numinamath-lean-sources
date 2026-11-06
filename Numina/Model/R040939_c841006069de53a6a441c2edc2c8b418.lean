import Mathlib

theorem number_theory_110877 (a : ℤ) : 5 ∣ a ^ 2 ↔ 5 ∣ a := by 
  constructor
  · -- Assume 5 divides a^2
    intro h
    have h1 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
      omega
    have h2 : a ^ 2 % 5 = 0 := by
      omega
    have h3 : a % 5 = 0 := by
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> 
        simp [pow_two, Int.mul_emod, Int.add_emod, h1] at h2 <;> omega
    have h4 : 5 ∣ a := by
      omega
    exact h4
  · -- Assume 5 divides a
    intro h
    obtain ⟨k, hk⟩ := h
    use 5 * (k ^ 2)
    rw [hk]
    ring