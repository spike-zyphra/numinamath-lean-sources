import Mathlib

/- An arithmetic sequence with first term $1$ has a common difference of $6$. A second sequence begins with $4$ and has a common difference of $7$. In the range of $1$ to $100$, what is the largest number common to both sequences? -/
theorem number_theory_11193{seq1 seq2:ℕ → ℕ}
  (hseq1: seq1 = fun n => 1+6*n)(hseq2: seq2 = fun n => 4+7*n) :
  IsGreatest {x | ∃ m n, x = seq1 m ∧ x = seq2 n ∧ 1 ≤ x ∧ x ≤ 100} 67
  := by
  rw [IsGreatest, upperBounds]; simp
  constructor
  · --verify 67 is common to both sequence. notice that 67 = 1 + 6x11 = 4+7x9
    rw [hseq1, hseq2]; simp; constructor
    use 11; use 9
  · -- show common number less than 100, ≤ 67
    intro m n hs12 ge1 le100
    -- seq1, seq2 are arithmetic sequence. since mth term of seq1 equal to nth term of seq2, we have the following equation.
    have eq1: 1+6*m = 4+7*n := by
      rw [hseq1, hseq2] at hs12; simp at hs12; apply hs12
    -- since 1+6m=4+7n, then 1+6m-4 must be multiple of 7.
    have hn: n ≥ 1 := by
      by_contra! hc
      have ht1: n = 0 := by linarith [hc]
      rw [ht1] at eq1; simp at eq1
      have ht2: 6*m = 3 := by omega
      omega
    have dv1: 7 ∣ 1+6*m-4 := by
      use n; rw [eq1]
      omega
    --let's try some possible values:
    --m=1, 1+6m-4=3, fails; m=2, 1+6m-4=9; fails;
    --m=3, 1+6m-4=15, fails; m=4, 1+6m-4=21, ok. so m ≥ 4
    have mge: m ≥ 4 := by
      by_contra! hc
      -- if natural number m < 4, then it can only be 0,1,2,3. and all these values fails to satisfy 1+6m=4+7n, or 7 ∣ 1+6m-4
      interval_cases m <;> simp at eq1 <;> simp at dv1
      · omega
      · norm_num at dv1
      · norm_num at dv1
      · norm_num at dv1
    -- when m=4, that common term is 25. so common number ≥ 25
    have hlb: seq1 m ≥ 25 := by
      rw [hseq1]; simp; linarith [mge]
    -- and when common term = 25, we solve n=3. so n ≥ 3
    have nge: n ≥ 3 := by
      have: 4+7*n ≥ 25 := by
        rw [← eq1]; linarith [mge]
      linarith [this]
    -- 25 is a common term, and from that common term on, next common term must satisfy difference is multiple of 6 and 7. or, their difference mod 6 and mod 7 are both zero.
    have hmod1: seq1 m - 25 ≡ 0 [MOD 6] := by
      have ht1: seq1 m - 25 = 6 * (m-4) := by
        rw [hseq1]; simp; omega
      rw [ht1]
      have ht2: 6 ∣ 6*(m-4) := by
        exact Nat.dvd_mul_right 6 (m - 4)
      exact Nat.modEq_zero_iff_dvd.mpr ht2
    have hmod2: seq1 m - 25 ≡ 0 [MOD 7] := by
      have: 7 ∣ seq1 m - 25 := by
        rw [hs12, hseq2]; simp; omega
      apply Nat.modEq_zero_iff_dvd.mpr this
    -- since 6 and 7 coprime, we have m-25 mod 6x7 ≡ 0
    have hmod3: seq1 m - 25 ≡ 0 [MOD 6*7] := by
      have hp: Nat.Coprime 6 7 := by norm_num
      apply (Nat.modEq_and_modEq_iff_modEq_mul hp).mp ⟨hmod1,hmod2⟩
    have hdv: 42 ∣ seq1 m - 25 := Nat.dvd_of_mod_eq_zero hmod3
    rcases hdv with ⟨d,hd⟩
    -- since difference of the next common number with 25 is multiple of 42, it can only be 25, 25+42=67. and 67+42 > 100 exceeds, so 67 is the largest number we find.
    by_cases hhd: d ≤ 1
    · omega
    · push_neg at hhd
      have: d ≥ 2 := by linarith [hhd]
      have gt100: seq1 m > 100 := by omega
      linarith [le100, gt100]