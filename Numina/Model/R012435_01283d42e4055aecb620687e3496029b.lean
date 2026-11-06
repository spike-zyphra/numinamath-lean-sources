import Mathlib

theorem number_theory_160659 {a : ℕ → ℕ} (ha1 : a 1 = 3)
    (han : ∀ n ≥ 2, a n = 3 ^ a (n - 1)) :
    (a 1990) % 10 = 7 := by 
  have h1 : ∀ n, a (n + 1) % 4 = 3 := by 
    intro n
    have h2 : ∀ (n : ℕ), a (n + 1) % 4 = 3 := by
      intro n
      induction n with
      | zero =>
        simp [ha1]
      | succ n ih =>
        have h3 : a (n + 2) = 3 ^ a (n + 1) := by
          specialize han (n + 2) (by omega)
          simpa using han
        rw [h3]
        have h4 : a (n + 1) % 4 = 3 := ih
        have h5 : (3 ^ a (n + 1)) % 4 = 3 := by
          have h6 : ∀ k, (3 ^ (4 * k + 3)) % 4 = 3 := by
            intro k
            induction k with
            | zero =>
              norm_num
            | succ k ih =>
              simp [Nat.pow_add, Nat.pow_mul, Nat.pow_succ] at ih ⊢
              all_goals omega
          have h7 : ∃ k, a (n + 1) = 4 * k + 3 := by
            have h8 : a (n + 1) % 4 = 3 := h4
            refine ⟨(a (n + 1) - 3) / 4, by omega⟩
          rcases h7 with ⟨k, hk⟩
          rw [hk]
          apply h6 k
        exact h5
    apply h2 n
  have h4 : a 1990 % 4 = 3 := by 
    apply h1
  have h3 : a 1990 = 3 ^ a 1989 := by
    specialize han 1990 (by omega)
    simpa using han
  rw [h3]
  have h5 : (3 ^ a 1989) % 10 = 7 := by
    have h7 : ∀ k, (3 ^ (4 * k + 3)) % 10 = 7 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_mul, Nat.pow_succ] at ih ⊢
        all_goals omega
    have h8 : ∃ k, a 1989 = 4 * k + 3 := by
      have h9 : a 1989 % 4 = 3 := by 
        apply h1
      refine ⟨(a 1989 - 3) / 4, by omega⟩
    rcases h8 with ⟨k, hk⟩
    rw [hk]
    apply h7 k
  exact h5