import Mathlib

/- Let $S, P, A, C, E$ be (not necessarily distinct) decimal digits where $E \neq 0$.
Given that $N=\sqrt{\overline{E S C A P E}}$ is a positive integer, find the minimum possible value of $N$. -/
theorem number_theory_610025:
  IsLeast {N: ℕ | ∃ (E S C A P: ℕ), E ≠ 0 ∧
    S < 10 ∧ P < 10 ∧ A < 10 ∧ C < 10 ∧ E < 10 ∧
    (N:ℝ) = √(Nat.ofDigits 10 [E, P, A, C, S, E]) } 319 := by
  -- obviously, overline(ESCAPE) = E10^5 + S10^4 + C10^3 + A10^2 + P10 + E
  have {E S C A P: ℕ}: (Nat.ofDigits 10 [E, P, A, C, S, E]:ℝ) =
    100000*E + 10000*S + 1000*C + 100*A + 10*P + E := by
    simp only [Nat.ofDigits]
    ring
  -- when E ≠ 0, that number ≥ 10^5. 300^2 is about 9 x 10^4, and problem asks for least such N.
  -- easy to guess a number of about 300.
  -- we prove 319 is the very numebr we find.
  rw [IsLeast, lowerBounds]
  simp only [Set.mem_setOf_eq]
  constructor
  · -- 319^2 = 101761
    -- so E,S,C,A,P = 1,0,1,7,6
    use 1,0,1,7,6
    rw [this]
    replace: (101761:ℝ) = 319^2 := by
      norm_num
    norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  · intro N
    rintro ⟨E, S, C, A, P, Enz, hS, hP, hA, hC, hE, hN⟩
    -- N^2 = 10^5E + 10^4S+...
    replace hN: N^2 = 100000*E + 10000*S + 1000*C + 100*A + 10*P + E := by
      rify
      rw [hN, this]
      apply Real.sq_sqrt ?_
      positivity
    -- E ≠ 0, so N^2 ≥ 10^5 > 316^2( = 99856)
    have hN1: N^2 > 316^2 := by
      have h1: N^2 ≥ 100000 := by
        have: E ≥ 1 := Nat.one_le_iff_ne_zero.mpr Enz
        rw [hN]
        linarith only [this]
      have h2: 100000 > 316^2 := by norm_num
      apply lt_of_lt_of_le h2 h1

    -- then N > 316, or N ≥ 317
    have hN2: N > 316 := by
      apply (pow_lt_pow_iff_left₀ ?_ ?_ (by norm_num)).mp hN1
      all_goals positivity
    replace hN2: N ≥ 317 := by exact hN2

    -- now we have N ≥ 317, and goal is N ≥ 319.
    -- it suffices to show 317, 318 does not satisfy.
    -- notice that last digit of N^2 is E.
    have hN3: N^2 % 10 = E := by
      norm_cast at this
      rw [hN, ← this, Nat.ofDigits]
      simp only [Nat.cast_id, Nat.add_mul_mod_self_left,
      Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd, hE]
    -- and 10^5E ≤ N^2
    have hN4: 10^5 * E ≤ N^2 := by
      rw [hN]
      linarith only
    have N_not_317_318: ¬ (N = 317 ∨ N = 318) := by
      rintro (rfl | rfl)
      all_goals
        -- N=317: last digit of 317^2 (=100489) is 9, E = 9.
        -- N = 318: last digit 318^2( = 101124) is 4, E = 4.
        norm_num at hN3
        -- but when E = 9 or 4, impossible for 317^2 ≥ 9 x 10^5 or 4x10^5
        simp [← hN3] at hN4
    -- N ≥ 317 but ≠ 317, ≠ 318, then N ≥ 319.
    omega