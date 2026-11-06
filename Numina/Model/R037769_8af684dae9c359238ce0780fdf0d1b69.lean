import Mathlib

theorem algebra_206099 (a : ℕ → ℤ) (h₀ : a 1 > a 0) (h₁ : a 1 > 0)
    (h₂ : ∀ r ∈ Finset.range 99, a (r + 2) = 3 * a (r + 1) - 2 * a r) :
    a 100 > 2 ^ 99 := by

  have h3 : ∀ (n : ℕ), n ≤ 98 → a (n + 2) = 3 * a (n + 1) - 2 * a n := by
    intro n hn
    have h4 : n < 99 := by omega
    specialize h₂ n (Finset.mem_range.mpr h4)
    simpa using h₂

  have h44 : a 100 = a 0 + (a 1 - a 0) * (2 ^ 100 - 1 : ℤ) := by
    norm_num at *
    have h4 : ∀ (n : ℕ), n ≤ 100 → a n = a 0 + (a 1 - a 0) * (2 ^ n - 1 : ℤ) := by
      intro n hn
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        simp
      | succ n =>
        cases n with
        | zero =>
          norm_num
          all_goals linarith
        | succ n =>
          have h6 : n ≤ 98 := by omega
          have eq1 : a (n + 2) = 3 * a (n + 1) - 2 * a n := h3 n h6
          have eq2 : a (n + 1) = a 0 + (a 1 - a 0) * (2 ^ (n + 1) - 1 : ℤ) := by
            apply ih
            all_goals omega
          have eq3 : a n = a 0 + (a 1 - a 0) * (2 ^ n - 1 : ℤ) := by
            apply ih
            all_goals omega
          rw [eq1, eq2, eq3]
          cases n with
          | zero =>
            all_goals norm_num
            all_goals ring
          | succ n =>
            simp [pow_two, pow_succ, mul_add, mul_sub_left_distrib, sub_eq_add_neg]
            all_goals ring_nf
            all_goals omega
    specialize h4 100 (by norm_num)
    simpa using h4

  rw [h44]
  norm_num
  omega