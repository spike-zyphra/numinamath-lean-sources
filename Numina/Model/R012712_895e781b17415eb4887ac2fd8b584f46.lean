import Mathlib

open Nat

theorem inequalities_199862 {n : ℕ} (hn : 2 ≤ n) :
    (2 * n) ! / (n !) ^ 2 > 4 ^ n / (n + 1 : ℝ) := by

  have h9 : (2 * n) ! * (n + 1) > 4 ^ n * (n !) ^ 2 := by
    have h10 : ∀ (k : ℕ), k ≥ 2 → (2 * k) ! * (k + 1) > 4 ^ k * (k !) ^ 2 := by
      intro k hk
      have h13 : k ≥ 2 := hk
      have base2 : (2 * 2) ! * (2 + 1) > 4 ^ 2 * (2 !) ^ 2 := by
        norm_num [Nat.factorial]
      have step2 : ∀ (m : ℕ), m ≥ 2 → (2 * m) ! * (m + 1) > 4 ^ m * (m !) ^ 2 → (2 * (m + 1)) ! * ((m + 1) + 1) > 4 ^ (m + 1) * ((m + 1) !) ^ 2 := by
        intros m hm h
        have eq2 : (2 * (m + 1)) ! = (2 * m + 2) * (2 * m + 1) * (2 * m) ! := by
          simp [Nat.factorial]
          all_goals
            ring
        have eq3 : (m + 1) ! = (m + 1) * (m) ! := by
          simp [Nat.factorial]
        have eq6 : (2 * (m + 1)) ! * ((m + 1) + 1) = (2 * m + 2) * (2 * m + 1) * (2 * m) ! * (m + 2) := by
          rw [eq2]
          all_goals
            ring
        have eq7 : 4 ^ (m + 1) * ((m + 1) !) ^ 2 = 4 ^ (m + 1) * ((m + 1) * (m) !) ^ 2 := by
          rw [eq3]
        rw [eq6, eq7]
        have h17 : (2 * m + 2) * (2 * m + 1) * (2 * m) ! * (m + 2) > 4 ^ (m + 1) * ((m + 1) * (m) !) ^ 2 := by
          have h14 : (2 * m) ! * (m + 1) > 4 ^ m * (m !) ^ 2 := h
          have eq10 : (4 ^ (m + 1) : ℕ) * ((m + 1) * (m) !) ^ 2 = 4 * (4 ^ m * (m + 1)^2 * (m !) ^ 2) := by
            ring_nf
          rw [eq10]
          have h18 : (2 * m + 2) * (2 * m + 1) * (2 * m) ! * (m + 2) > 4 * (4 ^ m * (m + 1)^2 * (m !) ^ 2) := by
            have h14 : (2 * m) ! * (m + 1) > 4 ^ m * (m !) ^ 2 := h
            nlinarith [sq_nonneg (m : ℕ), sq_nonneg ((m + 1 : ℕ) : ℕ), sq_nonneg ((m + 2 : ℕ) : ℕ), mul_nonneg (show 0 ≤ (m : ℕ) by linarith) (show 0 ≤ (m : ℕ) by linarith)]
          linarith
        linarith
      exact Nat.le_induction base2 step2 k (by linarith)
    specialize h10 n (by linarith)
    linarith

  have h11 : (2 * n) ! / (n !) ^ 2 > (4 ^ n / (n + 1 : ℝ)) := by
    have h12 : (2 * n) ! * (n + 1) > 4 ^ n * (n !) ^ 2 := h9
    have h13 : ( (2 * n) ! * (n + 1) : ℝ) > (4 ^ n * (n !) ^ 2 : ℝ) := by
      exact_mod_cast h12
    have h14 : ( (2 * n) ! : ℝ) / ( (n !) ^ 2 : ℝ) > (4 ^ n / (n + 1 : ℝ)) := by
      have h15 : ( (2 * n) ! : ℝ) * (n + 1 : ℝ) > (4 ^ n * (n !) ^ 2 : ℝ) := by
        exact_mod_cast h12
      have h20 : ( (2 * n) ! : ℝ) / ( (n !) ^ 2 : ℝ) > (4 ^ n / (n + 1 : ℝ)) := by
        have eq1 : ( (2 * n) ! : ℝ) * (n + 1 : ℝ) > (4 ^ n * (n !) ^ 2 : ℝ) := h15
        have h26 : ( (n !) ^ 2 * (n + 1 : ℝ) ) > 0 := by
          have h31 : (n ! : ℝ) > 0 := by
            have h32 : n ! > 0 := by
              apply Nat.factorial_pos
            exact_mod_cast h32
          have h33 : (n + 1 : ℝ) > 0 := by
            have h34 : (n : ℝ) ≥ (2 : ℝ) := by
              exact_mod_cast (show n ≥ 2 by linarith)
            nlinarith
          positivity
        have h21 : ( (2 * n) ! / ( (n !) ^ 2 : ℝ) ) * ( (n !) ^ 2 * (n + 1 : ℝ) ) > (4 ^ n / (n + 1 : ℝ)) * ( (n !) ^ 2 * (n + 1 : ℝ) ) := by
          have h24 : ( (2 * n) ! : ℝ) * (n + 1 : ℝ) - (4 ^ n * (n !) ^ 2 : ℝ) > 0 := by linarith
          have h25 : ( (2 * n) ! / ( (n !) ^ 2 : ℝ) ) * ( (n !) ^ 2 * (n + 1 : ℝ) ) - (4 ^ n / (n + 1 : ℝ)) * ( (n !) ^ 2 * (n + 1 : ℝ) ) = ( (2 * n) ! * (n + 1 : ℝ) - (4 ^ n * (n !) ^ 2 : ℝ) ) := by
            field_simp
            <;> nlinarith
          nlinarith
        have h30 : ( (2 * n) ! / ( (n !) ^ 2 : ℝ) ) > (4 ^ n / (n + 1 : ℝ)) := by
          apply (mul_lt_mul_right h26).mp
          linarith
        linarith
      linarith
    linarith
  exact h11