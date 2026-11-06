import Mathlib

theorem number_theory_173475 (a b : ℕ) (h₀ : a = b + 4) :
    ¬(a * b ≡ 31 [MOD 100]) := by 
  rw [h₀]
  intro h 
  have h1 : ((b + 4) * b) % 4 = 3 := by
    norm_num [Nat.ModEq] at h ⊢ 
    omega 
  have h2 : ((b + 4) * b) % 4 = (b ^ 2) % 4 := by 
    ring_nf 
    <;> omega 
  rw [h2] at h1 
  have h3 : (b ^ 2) % 4 = 0 ∨ (b ^ 2) % 4 = 1 := by 
    have h4 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
      omega 
    rcases h4 with (h4 | h4 | h4 | h4) <;> 
      simp [Nat.pow_mod, Nat.mul_mod, h4, Nat.mul_mod]
  omega