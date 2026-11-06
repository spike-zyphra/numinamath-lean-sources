import Mathlib


/- 1. If the set $S=\{n \mid n$ is an integer, and $22 n+2$ divides $2003 n+2004\}$, then $S$ is ( ).
(A) empty set $\varnothing$
(B) singleton set
(C) set with two elements
(D) infinite set -/
theorem number_theory_319233 {S : Set ℤ}
  (hS : S = {n:ℤ | 22*n+2 ∣ 2003*n+2004}) :
    S.encard = 2 := by

  -- if 22n+2 ∣ 2003n + 2004, then n is even.
  -- suppose n = 2k, then we have 22k+1 ∣ 7^2 x 409
  have h1 {n:ℤ} (hn: 22*n+2 ∣ 2003*n + 2004):
    ∃ (k:ℤ), n = 2*k ∧ 22*k+1 ∣ 7^2 * 409 := by
    -- n is even, since 22n+2 is even.
    have h1: Even n := by
      have: Even (22*n+2) := by
        have: 22*n+2 = 2*(11*n+1) := by ring
        rw [this]
        exact even_two_mul (11 * n + 1)
      replace: Even (2003*n+2004) := hn.even this
      replace: Even (2003*n) := by
        rw [Int.even_add] at this
        apply this.mpr (Int.even_iff.mpr rfl)
      rw [Int.even_mul] at this
      have: ¬ Even 2003 := Nat.not_even_iff.mpr rfl
      tauto
    rcases (even_iff_exists_two_mul.mp h1) with ⟨k, hk⟩
    rw [hk] at hn
    -- simplify
    have h2: 2003*(2*k) + 2004 =
      2 * (91*(22*k+1) + (k+911)) := by ring
    have h3: 22*(2*k) + 2 = 2 * (22*k+1) := by ring
    rw [h2, h3] at hn
    replace hn: 22*k+1 ∣ 91*(22*k+1) + (k+911) := by
      apply Int.dvd_of_mul_dvd_mul_left (by norm_num) hn
    replace hn: 22*k+1 ∣ k+911 := by
      refine (Int.dvd_iff_dvd_of_dvd_add hn).mp ?_
      apply Int.dvd_mul_left
    -- right side multiply 22
    replace hn: 22*k+1 ∣ 22*(k+911) := hn.mul_left 22
    have h4: 22*(k+911) = (22*k+1) + 7^2*409 := by ring
    rw [h4] at hn
    refine ⟨k, hk, ?_⟩
    exact dvd_add_self_left.mp hn

  -- if m divide 7^2 * 409,
  -- then m divide 409 or 7 divide m, since 7 and 409 are prime.
  have h2 {m: ℕ} (hm: m ∣ 7^2 * 409):
    m ∣ 409 ∨ 7 ∣ m := by
    by_cases h: 7 ∣ m
    · right; exact h
    · have p7: Nat.Prime 7 := by norm_num
      have co: Nat.Coprime m 7 := by
        refine Nat.coprime_comm.mp ?_
        exact (Nat.Prime.coprime_iff_not_dvd p7).mpr h
      replace co: Nat.Coprime m (7^2) := by
        exact Nat.Coprime.pow_right 2 co
      rw [co.dvd_mul_left] at hm
      left; exact hm

  -- if 22k+1 divide 7^2 x 409 for natural number k,
  -- it can only be 1.
  have h3 {k:ℕ} (h: 22*k+1 ∣ 7^2 * 409):
    k = 0 := by
    rcases (h2 h) with h2 | h2
    · -- 409 is prime. if 22k+1 divide 409, then it's 1 or 409.
      -- which is impossible.
      by_cases hk: k = 0
      · exact hk
      have: 22*k + 1 ≠ 1 := by
        apply ne_of_gt
        replace hk: 0 < k := Nat.zero_lt_of_ne_zero hk
        linarith only [hk]
      rw [Nat.Prime.dvd_iff_eq (by norm_num) this] at h2
      have: 22 ∣ 408 := by
        use k
        linarith only [h2]
      norm_num at this
    · rcases h2 with ⟨m, hm⟩
      -- if m divide 7 x 409, then m = 1,7,409,7x409.
      -- since 7,409 are distinct primes.
      replace h: m ∣ 7 * 409 := by
        rw [hm, pow_two, mul_assoc] at h
        apply Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
      have meq: m = 1 ∨ m = 7 ∨ m = 409 ∨ m = 7*409 := by
        have := Nat.le_of_dvd (by norm_num) h
        clear * - h this
        revert h
        native_decide +revert
      -- but all these cases are impossible.
      rcases meq with (meq | meq | meq | meq)
      all_goals
        norm_num [meq] at hm
        clear * - hm
        omega

  -- if 22k-1 divide 7^2 x 409, then only solution is k = 911
  -- this is because we observe no solution for 22k-1 < 49,
  -- therefore 22k-1 can only be 409, 7 x 409, 7^2 x 409.
  -- and we find only 7^2 x 409 satisfy.
  have h4 {k:ℕ} (h: 22*k - 1 ∣ 7^2 * 409): k = 911 := by
    have: k ≤ 911 := by
      have := Nat.le_of_dvd (by norm_num) h
      replace : 22*k ≤ 7^2*409+1 :=  Nat.le_add_of_sub_le this
      linarith only [this]
    clear * - h this
    revert h
    native_decide +revert

  -- then we claim set for 22k+1 divide 7^2 x 409 is 0 and -911.
  -- or, n = 0 or -1822
  have: S = {0, -1822} := by
    ext n
    rw [hS]
    simp only [Set.mem_setOf_eq, Int.reduceNeg, Set.mem_insert_iff,
    Set.mem_singleton_iff]
    constructor
    · intro h
      rcases (h1 h) with ⟨k, rfl, hk⟩
      -- cases on whether k ≥ 0 or < 0
      by_cases hhk: k ≥ 0
      · rw [← Int.natAbs_of_nonneg hhk] at hk
        norm_cast at hk
        specialize h3 hk
        simp only [Int.natAbs_eq_zero] at h3
        simp [h3]
      · replace hk: 22*(-k) - 1 ∣ 7^2 * 409 := by
          replace hk: -(22*k+1) ∣ 7^2 * 409 := Int.neg_dvd.mpr hk
          have: -(22*k+1) = 22*(-k) - 1 := by ring
          rwa [this] at hk
        push_neg at hhk
        rw [← Int.ofNat_natAbs_of_nonpos hhk.le] at hk
        have: (22:ℤ)*k.natAbs - 1 = ↑(22*k.natAbs - 1: ℕ) := by
          have: 0 < k.natAbs := Int.natAbs_pos.mpr hhk.ne
          replace: 1 ≤ k.natAbs := by exact this
          rw [Nat.cast_sub (by linarith only [this])]
          simp
        rw [this] at hk
        norm_cast at hk
        specialize h4 hk
        have keq: k = -911 := by
          zify at h4
          simp [← h4, abs_of_neg hhk]
        simp [keq]
    · rintro (rfl | rfl)
      <;> norm_num

  -- so two solutions.
  simp [this, Set.encard_pair]