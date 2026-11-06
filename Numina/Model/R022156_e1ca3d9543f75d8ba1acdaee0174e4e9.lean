import Mathlib

theorem number_theory_167831 :
    IsGreatest {k | ∀ n, Even n → Even (n + 2) → Even (n + 4) → Even (n + 6) →
      2^k ∣ n * (n + 2) * (n + 4) * (n + 6)} 7 := by
  constructor
  · -- Show 7 is in the set.
    intro n hn1 hn2 hn3 hn4
    rcases hn1 with ⟨k, rfl⟩
    have h1 : 2 ^ 7 ∣ (2 * k) * (2 * k + 2) * (2 * k + 4) * (2 * k + 6) := by
      have h2 : (2 * k) * (2 * k + 2) * (2 * k + 4) * (2 * k + 6) = 16 * (k * (k + 1) * (k + 2) * (k + 3)) := by
        ring_nf
      rw [h2]
      have h3 : k * (k + 1) * (k + 2) * (k + 3) % 8 = 0 := by
        have h4 : ∀ k : ℕ, k * (k + 1) * (k + 2) * (k + 3) % 8 = 0 := by
          intro k
          have h5 : k * (k + 1) * (k + 2) * (k + 3) % 8 = 0 := by
            have h5' : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by omega
            rcases h5' with (h | h | h | h | h | h | h | h) <;> 
              simp [h, Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
            all_goals omega
          exact h5
        exact h4 k
      have h4 : 2 ^ 7 ∣ 16 * (k * (k + 1) * (k + 2) * (k + 3)) := by
        have h6 : k * (k + 1) * (k + 2) * (k + 3) % 8 = 0 := h3
        have h7 : ∃ m, k * (k + 1) * (k + 2) * (k + 3) = 8 * m := by
          refine' ⟨k * (k + 1) * (k + 2) * (k + 3) / 8, by 
            omega⟩
        rcases h7 with ⟨m, hm⟩
        use m
        rw [hm]
        all_goals ring_nf <;> omega
      exact h4 
    have eq1 : (2 * k) * (2 * k + 2) * (2 * k + 4) * (2 * k + 6) = (k + k) * (k + k + 2) * (k + k + 4) * (k + k + 6) := by 
      ring
    rw [eq1] at h1
    exact h1
  · -- Show 7 is the greatest element in the set.
    intro k hk
    have h : ∀ n, Even n → Even (n + 2) → Even (n + 4) → Even (n + 6) → 2 ^ k ∣ n * (n + 2) * (n + 4) * (n + 6) := hk
    have h2 := h 2 (by decide) (by decide) (by decide) (by decide)
    by_contra h3
    push_neg at h3
    have h3' : k ≥ 8 := by omega
    have h4 : 2 ^ 8 ∣ 2 * 4 * 6 * 8 := by 
      have h5 : 2 ^ k ∣ 2 * 4 * 6 * 8 := h2
      have h6 : k ≥ 8 := by omega
      have h7 : 2 ^ 8 ∣ 2 ^ k := by 
        exact pow_dvd_pow _ (by omega)
      have h8 : 2 ^ 8 ∣ 2 * 4 * 6 * 8 := by 
        exact dvd_trans h7 h5
      exact h8
    norm_num at h4
    all_goals omega