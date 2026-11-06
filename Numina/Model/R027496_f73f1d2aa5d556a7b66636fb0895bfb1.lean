import Mathlib

open BigOperators

theorem number_theory_3934 : ((7^(7^2019)) % 100 = 43) := by 
  have h1 : (7 ^ (7 ^ 2019) ) % 100 = 43 := by
    have h2 : (7 ^ (7 ^ 2019) ) % 100 = 43 := by
      have h3 : ∀ k : ℕ, (7 ^ (4 * k + 3) ) % 100 = 43 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          have h4 : (7 ^ (4 * (k + 1) + 3) ) = (7 ^ (4 * k + 3) ) * (7 ^ 4) := by 
            ring_nf
          rw [h4]
          simp [Nat.mul_mod, ih] at *
          <;> norm_num
          <;> omega
      have h4 : (7 ^ 2019 ) % 4 = 3 := by
        norm_num [Nat.pow_mod]
      have h5 : ∃ k : ℕ, (7 ^ 2019 ) = 4 * k + 3 := by
        have h4' : (7 ^ 2019 ) % 4 = 3 := h4
        refine' ⟨(7 ^ 2019 ) / 4, by omega⟩
      rcases h5 with ⟨k, hk⟩
      have h7 : 7 ^ (7 ^ 2019) = 7 ^ (4 * k + 3) := by
        rw [show 7 ^ 2019 = 4 * k + 3 by omega]
      rw [h7]
      exact h3 k
    exact h2
  exact h1