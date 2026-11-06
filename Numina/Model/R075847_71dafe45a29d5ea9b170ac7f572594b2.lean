import Mathlib

theorem algebra_246745 {a b : ℤ} (ha : a > b) (hodd : Odd (2 * a + 1) ∧ Odd (2 * b + 1)) :
    8 ∣ (4 * (a * (a + 1) - b * (b + 1))) := by
  have h1 : a * (a + 1) % 2 = 0 := by
    have h1 : a % 2 = 0 ∨ a % 2 = 1 := by 
      omega 
    rcases h1 with (h1 | h1)
    · 
      simp [h1, Int.mul_emod, Int.add_emod] 
    · 
      simp [h1, Int.mul_emod, Int.add_emod] 
  have h2 : b * (b + 1) % 2 = 0 := by 
    have h1 : b % 2 = 0 ∨ b % 2 = 1 := by 
      omega 
    rcases h1 with (h1 | h1)
    · 
      simp [h1, Int.mul_emod, Int.add_emod] 
    · 
      simp [h1, Int.mul_emod, Int.add_emod] 
  have h3 : (a * (a + 1) - b * (b + 1)) % 2 = 0 := by 
    omega 
  obtain ⟨k, hk⟩ := show 2 ∣ (a * (a + 1) - b * (b + 1)) by 
    omega 
  use k 
  linarith [hk]