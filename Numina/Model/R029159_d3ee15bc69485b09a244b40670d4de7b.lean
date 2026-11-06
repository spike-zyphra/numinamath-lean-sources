import Mathlib

theorem number_theory_607548 : {n : ℕ | IsSquare (2 ^ n + 12 ^ n + 2011 ^ n)} = {1} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume that $2^n + 12^n + 2011^n$ is a perfect square, prove that $n = 1$.
    intro h
    rcases h with ⟨r, hr⟩
    by_cases h1 : n = 1
    · -- If $n = 1$, it is trivial.
      tauto
    · -- If $n \ne 1$.
      have h2 : n ≥ 2 := by
        by_contra!
        have : n = 0 := by
          omega
        rw [this] at hr
        have h3 : r ≤ 1 := by
          nlinarith
        interval_cases r <;> omega
      by_cases h4 : n % 2 = 0
      · -- If n is even
        have h5 : (2 ^ n + 12 ^ n + 2011 ^ n) % 3 = 2 := by
          have h1 : n % 2 = 0 := h4
          have h21 : (2 ^ n) % 3 = 1 := by
            have h11 : ∀ k : ℕ, (2 ^ (2 * k)) % 3 = 1 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [pow_succ, pow_mul] at ih ⊢
                omega
            have h12 : ∃ k, n = 2 * k := by
              refine' ⟨n / 2, by omega⟩
            rcases h12 with ⟨k, hk⟩
            rw [show n = 2 * k by linarith]
            apply h11 k
          have h22 : (12 ^ n) % 3 = 0 := by
            have h12 : ∀ k : ℕ, (12 ^ (k + 1)) % 3 = 0 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [pow_succ] at ih ⊢
                all_goals omega
            specialize h12 (n - 1)
            have h13 : n - 1 + 1 = n := by omega
            rw [h13] at h12
            omega
          have h23 : (2011 ^ n) % 3 = 1 := by
            have h11 : ∀ k : ℕ, (2011 ^ (k + 1)) % 3 = 1 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [pow_succ] at ih ⊢
                all_goals omega
            specialize h11 (n - 1)
            have h12 : n - 1 + 1 = n := by omega
            rw [h12] at h11
            omega
          omega
        have h6 : (r : ℕ) ^ 2 % 3 = 0 ∨ (r : ℕ) ^ 2 % 3 = 1 := by
          have h1 : (r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2) := by
            omega
          rcases h1 with (h1 | h1 | h1)
          · -- r % 3 = 0
            simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
          · -- r % 3 = 1
            simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
          · -- r % 3 = 2
            simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
        have h7 : (r : ℕ) ^ 2 = (2 ^ n + 12 ^ n + 2011 ^ n) := by
          linarith [hr]
        omega
      · -- n is odd.
        have h8 : n % 2 = 1 := by
          omega
        by_cases h9 : n ≥ 3
        · -- n ≥ 3.
          have h5 : (2 ^ n + 12 ^ n + 2011 ^ n) % 8 = 3 := by
            have h81 : n % 2 = 1 := h8
            have h111 : (2 ^ n) % 8 = 0 := by
              have h11 : ∀ k : ℕ, (2 ^ (k + 3)) % 8 = 0 := by
                intro k
                induction k with
                | zero =>
                  norm_num
                | succ k ih =>
                  simp [pow_succ] at ih ⊢
                  all_goals omega
              specialize h11 (n - 3)
              have h12 : n - 3 + 3 = n := by omega
              rw [h12] at h11
              omega
            have h221 : (12 ^ n) % 8 = 0 := by
              have h121 : ∀ k : ℕ, (12 ^ (k + 2)) % 8 = 0 := by
                intro k
                induction k with
                | zero =>
                  norm_num
                | succ k ih =>
                  simp [pow_succ] at ih ⊢
                  all_goals omega
              specialize h121 (n - 2)
              have h122 : n - 2 + 2 = n := by omega
              rw [h122] at h121
              omega
            have h331 : (2011 ^ n) % 8 = 3 := by
              have h111 : ∀ k : ℕ, (2011 ^ (2 * k + 1)) % 8 = 3 := by
                intro k
                induction k with
                | zero =>
                  norm_num
                | succ k ih =>
                  simp [pow_succ, pow_mul] at ih ⊢
                  all_goals omega
              have h14 : ∃ k, n = 2 * k + 1 := by
                refine' ⟨(n - 1) / 2, by omega⟩
              rcases h14 with ⟨k, hk⟩
              rw [show n = 2 * k + 1 by linarith]
              apply h111 k
            omega
          have h7 : (r : ℕ) ^ 2 % 8 = 0 ∨ (r : ℕ) ^ 2 % 8 = 1 ∨ (r : ℕ) ^ 2 % 8 = 4 := by
            have h1 : r % 8 = 0 ∨ r % 8 = 1 ∨ r % 8 = 2 ∨ r % 8 = 3 ∨ r % 8 = 4 ∨ r % 8 = 5 ∨ r % 8 = 6 ∨ r % 8 = 7 := by
              omega
            rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
            all_goals omega
          have h72 : (r : ℕ) ^ 2 = (2 ^ n + 12 ^ n + 2011 ^ n) := by
            linarith [hr]
          omega
        · -- n < 3, and n ≥ 2. Therefore n = 2.
          have h10 : n = 2 := by
            omega
          rw [h10] at hr
          norm_num at hr
          have h4 : r ≤ 2012 := by
            nlinarith
          interval_cases r <;> omega
  · -- Assume that $n = 1$, prove that $2^n + 12^n + 2011^n$ is a perfect square.
    intro h
    rw [h]
    native_decide