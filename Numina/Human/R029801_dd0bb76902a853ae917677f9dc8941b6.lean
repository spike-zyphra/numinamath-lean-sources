import Mathlib

open Real

/- 22nd Eötvös 1915 Problem 1 Given any reals A, B, C,
 show that An 2 + Bn + C < n! for all sufficiently large integers n. -/

theorem inequalities_123944 (A B C : ℝ) :
    ∃ N, ∀ n : ℕ, N ≤ n → A * n ^ 2 + B * n + C < Nat.factorial n := by

    -- we first show an inequlity between factorials
    have ineq: ∀ n: ℕ, 5 < n → 2 * n * (n - 1) * (n - 2) < Nat.factorial n := by
      intro n hn
      induction' n with n ih
      .
        norm_num at hn
      .
        by_cases ln: n = 5
        .
          simp [ln]
          decide
        .
          replace ln: 5 < n := by omega
          clear hn
          simp [ln] at ih
          have o1: n.factorial = n * (n - 1).factorial := by
            rw [show n = n - 1 + 1 by omega]
            rw [Nat.factorial_succ]
            simp
          rw [o1] at ih
          replace ih: 2 * (n - 1) * (n - 2) < Nat.factorial (n - 1) := by
            nlinarith
          have o2: (n + 1).factorial = (n + 1) * n.factorial := by
            rw [Nat.factorial_succ]
          rw [o2]
          clear o2
          have f: 2 * (n + 1 - 1) * (n + 1 - 2) < n.factorial := by
            rw [show n + 1 - 1 = n by simp]
            rw [show n + 1 - 2 = n - 1 by simp]
            rw [o1]
            clear o1
            have o3: 2 * n * (n - 1) < n * 2 * (n - 1) * (n - 2) := by
              rw [show n * 2 * (n - 1) * (n - 2) = (2 * n * (n - 1)) * (n - 2) by ring]
              have r: 1 < n - 2 := by omega
              rw [Nat.lt_mul_iff_one_lt_right]
              exact r
              have g1: 0 < n := by omega
              have g2: 0 < n - 1 := by omega
              nlinarith

            nlinarith

          nlinarith

    let d:= |A| + |B| + |C|
    let s:= max 6 (3 * d + 1)
    let N:= (⌊s⌋ + 1).natAbs

    -- we show that N is as desired

    use N
    -- show 6 ≤ N
    have lN1: 6 ≤ N := by
      have o1: 6 ≤ s := by
        simp [s]
      simp [N]
      zify
      have o:= le_abs_self (⌊s⌋ + 1)
      have o2: 5 ≤ ⌊s⌋ := by
        rw [Int.le_floor]
        simp
        linarith
      nlinarith
    -- show 3 * d + 1 ≤ N
    have lN2: 3 * d + 1 ≤ N := by
      have o1: 3 * d + 1 ≤ s := by
        simp [s]
      simp [N]
      have o2: ⌊3 * d + 1⌋ + 1 ≤ (⌊s⌋ + 1).natAbs := by
        rw [Int.natCast_natAbs]
        have o:= le_abs_self (⌊s⌋ + 1)
        apply Int.floor_le_floor  at o1
        nlinarith
      have o3: 3 * d + 1 ≤ ⌊3 * d + 1⌋ + 1 := by
        simp
        have o:= Int.lt_floor_add_one (3 * d)
        linarith
      have o4: ↑⌊3 * d + 1⌋ + (1: ℝ) ≤ ↑(⌊s⌋ + 1).natAbs := by
        rify at o2
        have i: 6 ≤ s := by
              simp [s]
        have j:= Int.lt_floor_add_one s
        have t: 5 < ⌊s⌋ := by
          rify
          linarith
        have r: ↑(⌊s⌋ + 1).natAbs = |⌊s⌋ + (1: ℝ)| := by
          have o: |↑⌊s⌋ + (1: ℝ)| = ↑⌊s⌋ + 1 := by
            apply abs_of_nonneg
            linarith
          rw [o]
          set f:= ⌊s⌋
          clear * - t
          clear_value f
          set g:= f + 1
          rw [show f + (1: ℝ) = g by simp [g]]
          have v: (g.natAbs: ℝ) = ↑(g.natAbs: ℤ) := by
            rw [← NNReal.coe_natCast]
            rfl
          rw [v]
          simp
          simp [g]
          omega
        rw [r]
        exact o2
      linarith

    clear_value N
    clear_value s
    have oa:= abs_nonneg A
    have ob:= abs_nonneg B
    have oc:= abs_nonneg C
    have d1: A ≤ d := by
      simp [d]
      have o:= le_abs_self A
      linarith
    have d2: B ≤ d := by
      simp [d]
      have o:= le_abs_self B
      linarith
    have d3: C ≤ d := by
      simp [d]
      have o:= le_abs_self C
      linarith
    intro n hn
    have ln1: 6 ≤ n := by omega
    have ln2: 3 * d + 1 ≤ n := by
      rify at hn
      linarith
    clear lN1
    clear lN2 hn
    have f1: A * ↑n ^ 2 + B * ↑n + C ≤ d * (↑n ^ 2 + ↑n + 1) := by
      nlinarith
    have f2: ↑n ^ 2 + ↑n + (1: ℝ) ≤ 3 * n ^ 2 := by
      have o1: n ≤ n ^ 2 := by
        rw [show n = n ^ 1 by simp]
        apply pow_le_pow
        simp
        simp
        omega
        norm_num
      rify at o1 ln1
      nlinarith
    have f3: 3 * d * n ^ 2 < Nat.factorial n := by
      specialize ineq n ln1
      have o1: ↑(n - 1) = n - (1: ℝ) := by
        rw [Nat.cast_sub]
        simp
        omega
      have o2: ↑(n - 2) = n - (2: ℝ) := by
        rw [Nat.cast_sub]
        simp
        omega
      have f: 3 * d * ↑n ^ 2 < 2 * n * (n - 1) * (n - 2) := by
        have x1: 3 * d ≤ n - 1 := by
          linarith
        have x2: n < 2 * (n - 2) := by
          omega
        rify at x2
        rw [o2] at x2
        rw [show (n: ℝ) ^ 2 = n * n by ring]
        calc
          3 * d * (↑n * ↑n) ≤ ((↑n - 1) * ↑n) * ↑n := by nlinarith
                          _ < ((↑n - 1) * ↑n) * (2 * (↑n - 2)) := by apply mul_lt_mul_of_pos_left; exact x2; rify at ln1; nlinarith
                          _ = 2 * n * (n - 1) * (n - 2) := by ring
      rify at ineq
      rw [o1, o2] at ineq
      nlinarith
      
    -- combine f1, f2, f3, we obtain the result
    nlinarith