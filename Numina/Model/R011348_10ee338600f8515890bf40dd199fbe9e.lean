import Mathlib

theorem number_theory_116412 : 2022 ^ 2022 ^ 2022 % 11 = 5 := by
  have h1 : (2022 ^ 2022 ^ 2022) % 11 = 5 := by
    have h2 : ∀ k : ℕ, (2022 ^ (10 * k + 4) ) % 11 = 5 := by
      intro k 
      induction k with 
      | zero =>
        norm_num 
      | succ k ih =>
        have h8 : (2022 ^ (10 * (k + 1) + 4)) % 11 = (2022 ^ (10 * k + 4 + 10)) % 11 := by ring_nf
        rw [h8]
        have h9 : (2022 ^ (10 * k + 4 + 10)) % 11 = (2022 ^ (10 * k + 4) * 2022 ^ 10) % 11 := by ring_nf 
        rw [h9]
        simp [Nat.mul_mod, ih] at *
        <;> norm_num 
    have h3 : (2022 ^ 2022 ) % 10 = 4 := by
      norm_num [Nat.pow_mod] 
    have h4 : ∃ k : ℕ, 2022 ^ 2022 = 10 * k + 4 := by
      refine' ⟨(2022 ^ 2022 - 4) / 10, by omega⟩ 
    rcases h4 with ⟨k, hk⟩
    have h5 : (2022 ^ 2022 ^ 2022) % 11 = 5 := by
      rw [show 2022 ^ 2022 ^ 2022 = 2022 ^ (2022 ^ 2022) by rfl] 
      rw [show 2022 ^ 2022 = 10 * k + 4 by linarith] 
      apply h2 k 
    exact h5 
  exact h1