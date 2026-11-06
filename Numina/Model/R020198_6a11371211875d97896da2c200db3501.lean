import Mathlib

theorem number_theory_304279 (n : ℕ) : 2016 ∣ ((n^2 + n)^2 - (n^2 - n)^2) * (n^6 - 1) := by
  have h1 : ((n^2 + n) ^ 2 - (n^2 - n) ^ 2) = 4 * n ^ 3 := by
    cases n with
    | zero =>
      all_goals simp
    | succ n =>
      cases n with
      | zero =>
        all_goals simp
      | succ n =>
        simp [Nat.pow_succ, Nat.mul_succ, Nat.pow_mul] at *
        <;> ring_nf
        <;> omega
  rw [h1]
  have h2 : 2016 ∣ 4 * n ^ 3 * (n ^ 6 - 1) := by
    have h2' : 4 * n ^ 3 * (n ^ 6 - 1) = 4 * (n ^ 9 - n ^ 3) := by
      cases n with
      | zero =>
        all_goals simp
      | succ n =>
        cases n with
        | zero =>
          all_goals simp
        | succ n =>
          simp [Nat.pow_succ, Nat.mul_sub, Nat.pow_mul] at *
          <;> ring_nf
          <;> omega
    rw [h2']
    -- Prove 2016 divides 4*(n^9 - n^3).
    -- Check that n^9 -n^3 is divisible by 8,9,7.
    have h8div : (n ^ 9 - n ^ 3) % 8 = 0 := by
      have h10 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
        omega
      rcases h10 with (h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq] 
    -- Prove divisibility by 9
    have h9div : (n ^ 9 - n ^ 3) % 9 = 0 := by
      have h11 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
        omega
      rcases h11 with (h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
    -- Prove divisibility by 7
    have h7div : (n ^ 9 - n ^ 3) % 7 = 0 := by
      have h12 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
        omega
      rcases h12 with (h | h | h | h | h | h | h) <;> simp [h, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
    -- Now from divisibility by 8, 9, 7, prove divisibility by 2016.
    omega
  exact h2