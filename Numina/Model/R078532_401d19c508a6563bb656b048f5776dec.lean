import Mathlib

theorem number_theory_189431 (a b : ℤ) (h₀ : 4 ∣ a - b) : 16 ∣ (3 * a + 5 * b) ^ 2 := by 
  have h1 : a % 4 = b % 4 := by 
    omega 
  have h2 : (3 * a + 5 * b) % 4 = 0 := by 
    simp [Int.add_emod, Int.mul_emod, h1] 
    all_goals omega
  have h3 : 4 ∣ (3 * a + 5 * b) := by 
    omega 
  obtain ⟨k, hk⟩ := h3
  rw [hk]
  use k ^ 2
  ring