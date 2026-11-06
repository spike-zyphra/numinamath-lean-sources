import Mathlib

theorem algebra_122232 {a b c d : ℤ} (f : ℤ → ℤ) (hf : ∀ x, f x = a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hodd0 : Odd (f 0)) (hodd1 : Odd (f 1)) : ¬∃ x, f x = 0 := by
  have h1 : f 0 % 2 = 1 := by 
    obtain ⟨k, hk⟩ := hodd0 
    have : f 0 = 2 * k + 1 := by 
      exact_mod_cast hk 
    omega
  have h2 : f 1 % 2 = 1 := by
    obtain ⟨k, hk⟩ := hodd1 
    have : f 1 = 2 * k + 1 := by 
      exact_mod_cast hk 
    omega
  have h1' : d % 2 = 1 := by 
    have eq0 : f 0 = d := by 
      simp [hf]
    rw [eq0] at h1 
    exact h1 
  have h2' : (a + b + c + d) % 2 = 1 := by 
    have eq1 : f 1 = a + b + c + d := by 
      simp [hf]
      <;> ring 
    rw [eq1] at h2 
    exact h2 
  intro h 
  rcases h with ⟨x, hx⟩ 
  have h3 : f x = 0 := hx 
  rw [hf x] at h3 
  have h4 : (a * x ^ 3 + b * x ^ 2 + c * x + d) % 2 = 0 := by 
    omega 
  have h5 : x % 2 = 0 ∨ x % 2 = 1 := by 
    omega 
  rcases h5 with (h5 | h5) 
  · -- x is even 
    have h6 : x % 2 = 0 := h5 
    have h7 : x ^ 3 % 2 = 0 := by 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h6]
    have h8 : x ^ 2 % 2 = 0 := by 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h6]
    have h9 : (a * x ^ 3 + b * x ^ 2 + c * x + d) % 2 = 1 := by 
      simp [Int.add_emod, Int.mul_emod, h7, h8, h6, h1']
    omega 
  · -- x is odd 
    have h6 : x % 2 = 1 := h5 
    have h7 : x ^ 3 % 2 = 1 := by 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h6]
    have h8 : x ^ 2 % 2 = 1 := by 
      simp [pow_succ, Int.add_emod, Int.mul_emod, h6]
    have h9 : (a * x ^ 3 + b * x ^ 2 + c * x + d) % 2 = 1 := by 
      simp [Int.add_emod, Int.mul_emod, h7, h8, h6, h1']
      <;> omega 
    omega