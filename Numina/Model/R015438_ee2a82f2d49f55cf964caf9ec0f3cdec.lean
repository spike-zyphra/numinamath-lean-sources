import Mathlib

theorem number_theory_7096 (n : ℕ) (hn : n > 0) :
    37 ∣ (23^n + 14^n) ↔ ∃ k, n = 2 * k + 1 := by
  constructor
  · -- Assume 37 divides (23^n + 14^n), prove exists k, n = 2 * k + 1
    intro h
    by_cases h1 : n % 2 = 1
    · -- n is already odd
      refine ⟨n / 2, by omega⟩
    · -- n is even
      have h2 : n % 2 = 0 := by omega
      have h3 : ∃ m, n = 2 * m := by
        refine' ⟨n / 2, by omega⟩
      rcases h3 with ⟨m, hm⟩
      have h4 : (23 ^ n + 14 ^ n : Nat) % 37 = 0 := by
        omega
      have h5 : (23 ^ n + 14 ^ n) % 37 = (2 * (14 ^ (2 * m)) ) % 37 := by
        rw [show n = 2 * m by omega]
        have h6 : ∀ m : ℕ, (23 ^ (2 * m) + 14 ^ (2 * m) : Nat) % 37 = (2 * (14 ^ (2 * m)) ) % 37 := by
          intro m
          induction m with
          | zero =>
            norm_num
          | succ m ih =>
            simp [pow_succ, pow_mul, Nat.add_mod, Nat.mul_mod] at ih ⊢
            all_goals norm_num [Nat.add_mod, Nat.mul_mod] at ih ⊢
            all_goals omega
        specialize h6 m
        simpa using h6
      rw [h5] at h4
      have h7 : (2 * (14 ^ (2 * m) : Nat) ) % 37 ≠ 0 := by
        by_contra h0
        have h00 : (2 * (14 ^ (2 * m) ) ) % 37 = 0 := by omega
        have h01 : (14 ^ (2 * m) ) % 37 = 0 := by
          norm_num [Nat.mul_mod] at h00 ⊢
          all_goals omega
        have h8 : (14 : Nat) ^ (2 * m) % 37 = 0 := by
          omega
        have h9 : ∀ m : ℕ, (14 : Nat) ^ (2 * m) % 37 > 0 := by
          intro m
          induction m with
          | zero =>
            norm_num
          | succ m ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            all_goals norm_num at ih ⊢
            all_goals omega
        have h10 : (14 : Nat) ^ (2 * m) % 37 > 0 := h9 m
        omega
      omega
  · -- Assume exists k, n = 2 * k + 1, prove 37 divides (23^n + 14^n)
    intro h
    rcases h with ⟨k, hk⟩
    rw [show n = 2 * k + 1 by omega]
    have h : ∀ k : ℕ, (23 ^ (2 * k + 1) + 14 ^ (2 * k + 1) : Nat) % 37 = 0 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h1 : (23 ^ (2 * (k + 1) + 1) + 14 ^ (2 * (k + 1) + 1) : Nat) % 37 = 0 := by
          simp [pow_succ, pow_mul, Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals norm_num [Nat.add_mod, Nat.mul_mod] at ih ⊢
          all_goals omega
        exact h1
    have h1 : (23 ^ (2 * k + 1) + 14 ^ (2 * k + 1) : Nat) % 37 = 0 := h k
    omega