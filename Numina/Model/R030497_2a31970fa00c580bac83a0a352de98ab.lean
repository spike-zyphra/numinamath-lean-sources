import Mathlib

theorem number_theory_221776 {n : ℕ} (hn : Odd n) (hnsq : ∃ m, n = m^2) (hnsq9 : ¬ 9 ∣ n) :
    24 ∣ (n - 1) := by
  rcases hnsq with ⟨m, rfl⟩
  have h1_odd : (m ^ 2) % 2 = 1 := by 
    obtain ⟨k, hk⟩ := hn 
    have : (m ^ 2) = 2 * k + 1 := by linarith 
    omega 
  have h1 : m % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h3 : m % 2 = 0 := by 
      omega 
    have h4 : (m ^ 2) % 2 = 0 := by 
      simp [Nat.pow_mod, h3] 
    omega 
  have h2 : m ^ 2 % 8 = 1 := by
    have h11 : m % 2 = 1 := h1 
    have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by 
      omega 
    rcases this with (h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h3 : m ^ 2 % 3 = 1 := by
    have h4 : m % 3 = 1 ∨ m % 3 = 2 := by
      by_contra h8
      push_neg at h8 
      have h5 : m % 3 = 0 := by 
        omega 
      have h6 : m ^ 2 % 3 = 0 := by 
        simp [Nat.pow_mod, h5]
      have h7 : 9 ∣ m ^ 2 := by
        have h8 : m % 3 = 0 := h5 
        have h9 : 3 ∣ m := by 
          omega 
        have h10 : ∃ k, m = 3 * k := by 
          refine' ⟨m / 3, by 
            omega 
          ⟩ 
        rcases h10 with ⟨k, hk⟩ 
        have h11 : m ^ 2 = 9 * (k ^ 2) := by 
          rw [hk] 
          ring 
        omega 
      have h8 : ¬ (9 ∣ m ^ 2) := by 
        tauto 
      contradiction 
    rcases h4 with (h9 | h9) 
    · -- m ≡ 1 (mod 3)
      simp [Nat.pow_mod, h9] 
    · -- m ≡ 2 (mod 3)
      simp [Nat.pow_mod, h9]
  have h5 : (m ^ 2 - 1) % 8 = 0 := by 
    omega 
  have h6 : (m ^ 2 - 1) % 3 = 0 := by 
    omega 
  omega