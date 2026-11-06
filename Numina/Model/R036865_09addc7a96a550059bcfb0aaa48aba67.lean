import Mathlib

theorem number_theory_78054 (a b : ℕ) (ha : Odd a) (hb : Odd b) :
    ∃ k, (2^2018 ∣ b^k - a^2) ∨ (2^2018 ∣ a^k - b^2) := by 
  use 0
  have h1 : a % 2 = 1 := by
    obtain ⟨m, hm⟩ := ha
    omega
  have h2 : b % 2 = 1 := by
    obtain ⟨m, hm⟩ := hb
    omega
  have h3 : a ≥ 1 := by
    by_contra h
    push_neg at h
    have h4 : a < 1 := by omega
    have h5 : a % 2 = 0 := by
      omega
    omega
  have h4 : b ≥ 1 := by
    by_contra h
    push_neg at h
    have h5 : b < 1 := by omega
    have h6 : b % 2 = 0 := by
      omega
    omega
  have h5 : 1 - a ^ 2 = 0 := by
    have h7 : a ^ 2 ≥ 1 := by
      have h8 : a ≥ 1 := h3
      have h9 : a ^ 2 ≥ 1 := by
        have h10 : a ≥ 1 := h8
        have h11 : a ^ 2 ≥ 1 ^ 2 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        norm_num at h11 ⊢
        all_goals omega
      omega
    omega
  have h6 : 1 - b ^ 2 = 0 := by
    have h7 : b ^ 2 ≥ 1 := by
      have h8 : b ≥ 1 := h4
      have h9 : b ^ 2 ≥ 1 := by
        have h10 : b ≥ 1 := h8
        have h11 : b ^ 2 ≥ 1 ^ 2 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        norm_num at h11 ⊢
        all_goals omega
      omega
    omega
  left
  rw [show b ^ 0 = 1 by simp, show a ^ 2 = a ^ 2 by rfl]
  rw [h5]
  all_goals norm_num