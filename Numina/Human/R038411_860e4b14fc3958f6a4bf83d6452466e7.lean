import Mathlib

/-Find all four-digit positive integers abcd with a ≠ 0, such that
  10^3 * a + 10 ^ 2 * b + 10 * c + d = a ^ (a + b + c + d) -
  a ^ (-a + b - c + d) + a -/

  theorem number_theory_605125: {(a, b, c, d): ℕ × ℕ × ℕ × ℕ | a ≠ 0 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧
  a + c ≤ b + d ∧  10^3 * a + 10 ^ 2 * b + 10 * c + d = a ^ (a + b + c + d) - a ^ (b + d - a - c) + a}
  = {(2, 0, 1, 8)} := by

    ext ⟨a, b, c, d⟩
    constructor
    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      simp
      rcases h with ⟨ha, la, lb, lc, ld, l, h⟩
      have h1: a ≠ 1 := by
        by_contra! o
        simp [o] at h
        omega
      replace h1: 2 ≤ a := by
        omega

      -- then we prove an inequality to give an upper bound for a
      have ineq1: 10^3 * a + 10 ^ 2 * b + 10 * c + d > a ^ (a + b + c + d - 2) * (a ^ 2 - 1) := by
        have i: b + d - a - c ≤ a + b + c + d - 2 := by
          omega
        replace i: a ^ (b + d - a - c) ≤ a ^ (a + b + c + d - 2) := by
          apply pow_le_pow
          omega
          omega
          omega
        have j: a ^ (a + b + c + d) - a ^ (a + b + c + d - 2) = a ^ (a + b + c + d - 2) * (a ^ 2 - 1) := by
          have eq: a ^ (a + b + c + d) = a ^ (a + b + c + d - 2) * a ^ 2 := by
            have u: a + b + c + d - 2 + 2 = a + b + c + d := by
              omega
            nth_rewrite 1 [← u]
            ring
          rw [eq]
          have v: 1 ≤ a ^ 2 := by
            rw [show 1 = 1 ^ 2 by omega]
            apply pow_le_pow
            omega
            omega
            norm_num
          set t:= a ^ (a + b + c + d - 2)
          clear_value t
          zify
          rw [Int.natCast_sub]
          rw [Int.natCast_mul]
          rw [Int.natCast_sub]
          ring
          omega
          nlinarith

        calc
          10 ^ 3 * a + 10 ^ 2 * b + 10 * c + d  = a ^ (a + b + c + d) - a ^ (b + d - a - c) + a := by exact h
               _ ≥ a ^ (a + b + c + d) - a ^ (a + b + c + d - 2) + a := by omega
               _ > a ^ (a + b + c + d) - a ^ (a + b + c + d - 2) := by omega
               _ = a ^ (a + b + c + d - 2) * (a ^ 2 - 1) := by exact j

      have ineq2: 10000 > a ^ (2 * a - 2) * (a ^ 2 - 1) := by
          have f: 10000 > 10 ^ 3 * a + 10 ^ 2 * b + 10 * c + d := by
            nlinarith
          have g:  a ^ (a + b + c + d - 2) * (a ^ 2 - 1) ≥ a ^ (2 * a - 2) * (a ^ 2 - 1) := by
            simp
            have r: 2 * a - 2 ≤ a + b + c + d - 2 := by
              omega
            replace r: a ^ (2 * a - 2) ≤ a ^ (a + b + c + d - 2) := by
              apply pow_le_pow
              omega
              omega
              omega
            nlinarith
          calc
            10000 > 10 ^ 3 * a + 10 ^ 2 * b + 10 * c + d := by exact f
                _ > a ^ (a + b + c + d - 2) * (a ^ 2 - 1) := by exact ineq1
                _ ≥ a ^ (2 * a - 2) * (a ^ 2 - 1) := by exact g

    -- use this inequatity, we can prove that a ≤ 3
      replace la: a < 4 := by
        by_contra! o
        absurd ineq2
        simp
        have l1: 4 ^ 6 ≤ a ^ (2 * a - 2) := by
          apply pow_le_pow
          omega
          omega
          omega
        have l2: 15 ≤ a ^ 2 - 1 := by
          have o: 4 ^ 2 ≤ a ^ 2 := by
            apply pow_le_pow
            omega
            omega
            norm_num
          omega
        nlinarith
      clear ineq2

    -- hence a = 2 ∨ a = 3, we check them all
      replace la: a = 2 ∨ a = 3 := by
        omega
      rcases la with o | o
      -- cases a = 2
      .
        simp [o] at *
        have s: 0 ≤ 2 ^ (b + d - 2 - c) := by
          apply pow_nonneg
          omega
        have h2: 2000 ≤ 2 ^ (2 + b + c + d) + 2 := by
          omega
        have ineq2: 8 < b + c + d := by  -- we must have b + c + d > 8
          by_contra! v
          have x: 2 ^ (2 + b + c + d) ≤ 2 ^ 10 := by
            apply pow_le_pow
            omega
            norm_num
            omega
          absurd h2
          simp
          nlinarith
        have ineq3: b + c + d < 10 := by   -- we must have b + c + d < 10
          by_contra! v
          rw [show 2 + b + c + d - 2 = b + c + d by omega] at ineq1
          have x: 2 ^ 10 ≤ 2 ^ (b + c + d) := by
            apply pow_le_pow
            omega
            norm_num
            omega
          nlinarith
        -- then b + c + d = 9
        have t: b + c + d = 9 := by omega
        rw [show 2 + b + c + d =2 + (b + c + d) by omega] at h
        simp [t] at h
        -- then b = 0
        have ob: b = 0 := by
          by_contra!
          replace ob: 1 ≤ b := by omega
          have s1: 0 ≤ 2 ^ (b + d - 2 - c) := by
            apply pow_nonneg
            norm_num
          have s2: 2100 ≤ 2000 + 100 * b + 10 * c + d := by linarith
          rw [h] at s2
          absurd s2
          simp
          omega
        simp [ob] at *
        replace t: d = 9 - c := by
          omega
        simp [t] at *
        clear ineq1 ineq2 ineq3 h2 ha h1 o lb s ob ld lc
        replace l: c ≤ 3 := by omega
        interval_cases c
        <;> norm_num at h
        omega
      -- cases a = 3
      .
        simp [o] at *
        have s: 0 ≤ 3 ^ (b + d - 3 - c) := by
          apply pow_nonneg
          omega
        have h2: 3000 ≤ 3 ^ (3 + b + c + d) + 3 := by
          omega
        have ineq2: 5 ≤  b + c + d := by  -- we must have b + c + d > 4
          by_contra! v
          have x: 3 ^ (3 + b + c + d) ≤ 3 ^ 7 := by
            apply pow_le_pow
            omega
            norm_num
            omega
          absurd h2
          simp
          nlinarith

        -- then we can see contradiction in ineq1 since b + c + d is too large
        rw [show 3 + b + c + d - 2 = b + c + d + 1 by omega] at ineq1
        have x: 3 ^ 6 ≤ 3 ^ (b + c + d + 1) := by
            apply pow_le_pow
            omega
            norm_num
            omega
        absurd ineq1
        simp
        nlinarith

    -- the backward direction
    .
      intro h
      simp at h
      simp [h]