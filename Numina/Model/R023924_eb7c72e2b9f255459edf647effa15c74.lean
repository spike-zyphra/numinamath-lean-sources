import Mathlib

open Nat

theorem number_theory_93436 {I : ℕ → ℕ} (hI : ∀ k, I k = 10 ^ (k + 2) + 64) :
    IsGreatest {Nat.factorization (I k) 2 | k > 0} 7 := by
  constructor
  · -- Show 7 is attained.
    use 4
    constructor
    · norm_num
    · 
      rw [hI 4]
      native_decide
  · -- Show 7 is the greatest.
    intro x hx
    rcases hx with ⟨k, hk, rfl⟩
    have hk1 : k > 0 := hk
    have h2 : Nat.factorization (I k) 2 ≤ 7 := by
      rw [hI k]
      have h4 : Nat.factorization (10 ^ (k + 2) + 64) 2 ≤ 7 := by
        by_contra h
        push_neg at h
        have h12 : Nat.factorization (10 ^ (k + 2) + 64) 2 ≥ 8 := by omega
        have h13 : (10 ^ (k + 2) + 64) % 256 = 0 := by
          have h14 : 256 ∣ (10 ^ (k + 2) + 64) := by
            have h15 : Nat.factorization (10 ^ (k + 2) + 64) 2 ≥ 8 := h12
            have h16 : 2 ^ 8 ∣ (10 ^ (k + 2) + 64) := by
              have h17 : 2 ^ (Nat.factorization (10 ^ (k + 2) + 64) 2) ∣ (10 ^ (k + 2) + 64) := by
                apply Nat.ordProj_dvd
              have h18 : 2 ^ 8 ∣ 2 ^ (Nat.factorization (10 ^ (k + 2) + 64) 2) := by
                exact pow_dvd_pow _ (by omega)
              exact dvd_trans h18 h17
            have h19 : 2 ^ 8 = 256 := by norm_num
            rw [h19] at h16
            exact h16
          omega
        have h18 : (10 ^ (k + 2) + 64) % 256 = 0 := h13
        have h19 : k ≤ 4 := by
          by_contra h
          push_neg at h
          have h19 : k > 4 := by omega
          have h20 : k ≥ 5 := by omega
          have h21 : (10 ^ (k + 2) + 64) % 256 ≠ 0 := by
            have h22 : ∀ m : ℕ, (10 ^ (m + 5 + 2) + 64) % 256 ≠ 0 := by
              intro m
              induction m with
              | zero =>
                norm_num
              | succ m ih =>
                simp [Nat.pow_add, Nat.pow_mul, Nat.mul_add, Nat.mul_assoc] at ih ⊢
                all_goals omega
            specialize h22 (k - 5)
            have h23 : k - 5 + 5 + 2 = k + 2 := by omega
            rw [h23] at h22
            tauto
          omega
        interval_cases k <;> norm_num at h18 h19 ⊢
      linarith
    linarith