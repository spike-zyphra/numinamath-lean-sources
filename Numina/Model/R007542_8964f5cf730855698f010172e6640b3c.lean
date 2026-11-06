import Mathlib

theorem number_theory_131374 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    p^2 ≡ 1 [MOD 24] := by
  have h1 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have h2' : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h'
    push_neg at h'
    have h3 : p % 3 = 0 := by
      omega
    have h4 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals linarith
    contradiction
  have h3 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have h3 : p % 2 = 1 := h1
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      omega
    assumption
  have h4 : (p ^ 2) % 3 = 1 := by
    rcases h2 with (h2 | h2)
    · 
      simp [Nat.pow_mod, h2]
    · 
      simp [Nat.pow_mod, h2]
  have h5 : (p ^ 2) % 8 = 1 := by
    rcases h3 with (h3 | h3 | h3 | h3)
    · 
      simp [Nat.pow_mod, h3]
    · 
      simp [Nat.pow_mod, h3]
    · 
      simp [Nat.pow_mod, h3]
    · 
      simp [Nat.pow_mod, h3]
  norm_num [Nat.ModEq] at *
  omega