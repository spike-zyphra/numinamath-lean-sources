import Mathlib

theorem number_theory_173094 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    ((6 ∣ p - 1) ∧ ¬(6 ∣ p + 1)) ∨ (¬(6 ∣ p - 1) ∧ 6 ∣ p + 1) := by
  have hp2 : p % 2 = 1 := by 
    by_contra h1
    push_neg at h1
    have h2 : p % 2 = 0 := by 
      omega
    have h3 : ¬Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    tauto
  -- Show that p ≡ 1 or 2 (mod 3)
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h1
    push_neg at h1
    have h2 : p % 3 = 0 := by
      omega
    have h3 : 3 ∣ p := by 
      omega
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    tauto 
  -- Show that p ≡ 1 or 5 (mod 6)
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by
    omega 
  rcases hp6 with (h1 | h5)
  · -- Assume p % 6 = 1
    have h0 : p % 6 = 1 := h1
    have h11 : (6 ∣ p - 1) := by
      omega 
    have h12 : ¬ (6 ∣ p + 1) := by 
      omega 
    left 
    exact ⟨h11, h12⟩ 
  · -- Assume p % 6 = 5
    have h00 : p % 6 = 5 := h5 
    have h21 : ¬ (6 ∣ p - 1) := by 
      omega 
    have h22 : (6 ∣ p + 1) := by 
      omega 
    right
    exact ⟨h21, h22⟩