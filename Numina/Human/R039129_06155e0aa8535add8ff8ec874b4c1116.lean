import Mathlib
open Real

/- Determine all integers $n$ for which
$$
\sqrt{\frac{25}{2}+\sqrt{\frac{625}{4}-n}}+\sqrt{\frac{25}{2}-\sqrt{\frac{625}{4}-n}}
$$
is an integer. -/
theorem algebra_240518 (n : ℤ) :
    (625/(4: ℝ) - n ≥ 0) ∧ (25/2 + √ ((625/4 - n)) ≥ 0) ∧ (25/2 - √ ((625/4 - n)) ≥ 0) ∧
    (∃ k : ℤ, √ (25/2 + √ ((625/4 - n))) + √ (25/2 - √ ((625/4 - n))) = k)
    ↔ (n = 0 ∨ n = 144) := by

  have hsqrt4 : (4: ℝ) = 2 ^ 2 := by norm_num
  have hsqrt9 : (9: ℝ) = 3 ^ 2 := by norm_num
  have hsqrt16 : (16: ℝ) = 4 ^ 2 := by norm_num
  have hsqrt25 : (25: ℝ) = 5 ^ 2 := by norm_num
  have hsqrt49 : (49: ℝ) = 7 ^ 2 := by norm_num
  have hsqrt625 :(625: ℝ) = 25 ^ 2 := by norm_num
  constructor
  · intro h
    rcases h with ⟨hn1, hn2, hn3, h⟩
    have hn_nonneg: (n: ℝ) ≥ 0 := by
      by_contra! hnneg
      have : √ (625/4 - n: ℝ) > √ (625/4: ℝ) := by
        exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
      norm_num at this
      rw [hsqrt625, hsqrt4, sqrt_sq, sqrt_sq] at this
      norm_num at this
      have : ¬ 25 / 2 + √(625 / 4 - ↑n) ≥ 0 := by linarith
      contradiction
      simp; simp

    rcases h with ⟨p, hp⟩
    /- Let $$ p=\sqrt{\frac{25}{2}+\sqrt{\frac{625}{4}-n}}+
    \sqrt{\frac{25}{2}-\sqrt{\frac{625}{4}-n}} =\sqrt{25+2 \sqrt{n}} $$. -/
    have hsq := congrFun (congrArg HPow.hPow hp) 2
    ring_nf at hsq
    rw [sq_sqrt hn3, sq_sqrt hn2, ← sqrt_mul hn2 (25 / 2 - √(625 / 4 - ↑n))] at hsq
    ring_nf at hsq
    rw [sq_sqrt hn1] at hsq
    ring_nf at hsq
    rw [AddCommMagma.add_comm] at hsq
    have hsq2 : √↑n = (↑p ^ 2 - 25 ) / 2 := by linarith
    have := congrFun (congrArg HPow.hPow hsq2) 2

    -- Then $n=\left(\frac{p^{2}-25}{2}\right)^{2}$
    rw [sq_sqrt hn_nonneg] at this

    -- and obviously $p$ is an odd number not less than 5.
    have hp_odd : Odd p := by
      by_contra hpeven
      simp at hpeven
      rcases Even.exists_two_nsmul p hpeven with ⟨k, hk⟩
      simp at hk
      rw [hk] at this
      simp at this
      rw [show (2 * k: ℝ) ^ 2 - 25 = 4 * ↑(k ^ 2 - 6: ℤ) - 1 by field_simp; ring] at this
      set q := k ^ 2 - 6 with hq
      rw [show ((4 * q - 1: ℝ) / 2) ^ 2 = ↑(4 * q ^ 2 - 2 * q: ℤ) + 1 / 4 by field_simp; ring] at this
      set q' := 4 * ↑q ^ 2 - 2 * ↑q with hq'
      have hn1: n < (q' + 1: ℝ) := by linarith
      have hn1: n < q' + 1 := by
        by_contra! hcx
        have : ¬ (n: ℝ) < q' + 1 := by simp; norm_cast
        contradiction
      have hn2: n > (q': ℝ) := by linarith
      have hn2: n > q' := by
        by_contra! hcx
        have : ¬ (n: ℝ) > q' := by simp; norm_cast
        contradiction
      have : ¬ n < q' + 1 := by simp; exact hn2
      contradiction
    have hp_ge_5 : p ≥ 5 := by
      by_contra! hp_lt_5
      have : (p: ℝ) ≥ 0 := by rw [← hp]; positivity
      have : |(p: ℝ)| < |5| := by
        unfold abs; simp; apply And.intro; norm_cast; linarith;
      have := sq_lt_sq.mpr this
      norm_num at this
      rw [← hsq] at this
      field_simp at this
      have : ¬ √↑n * 2 < 0 := by simp
      contradiction

    -- we have $p < 9$, otherwise $n ⋗ \frac{625}{4}$ and the initial expression would be undefined.
    have hp_lt_9 : p < 9 := by
      by_contra! hp_ge_9
      have : (p: ℝ) ^ 2 ≥ 9 ^ 2 := by
        apply sq_le_sq.mpr; simp; unfold abs; simp; left
        exact Int.cast_le.mpr hp_ge_9
      have : (↑p ^ 2 - 25: ℝ) / 2 ≥ (9 ^ 2 - 25:ℝ) / 2 := by
        apply (div_le_div_iff_of_pos_right (by simp)).mpr
        apply tsub_le_tsub_right
        exact this
      rw [← hsq2] at this
      norm_num at this
      have : (28: ℝ) ^ 2 ≤ (√↑n) ^ 2 := by
        apply sq_le_sq'
        have : -√↑n ≤ 0 := by simp
        have : 28 > 0 := by simp
        linarith
        exact this
      rw [sq_sqrt] at this
      have : ¬ 625 / (4: ℝ) - (n: ℝ) ≥ 0 := by linarith
      contradiction
      exact hn_nonneg

    -- The two remaining values of $p$ are $p=5$ and $p=7$
    have hp_eq: p = 5 ∨ p = 7 := by
      interval_cases p
      all_goals simp
      have : Even 6 := by
        apply Nat.even_iff.mpr
        simp
      contradiction
      have : Even 8 := by
        apply Nat.even_iff.mpr
        simp
      contradiction

    -- which gives up $n=0$ and $n=144$ respectively.
    cases hp_eq with
    | inl hp1 =>
      left
      rw [hp1] at this
      norm_num at this
      exact this
    | inr hp2 =>
      right
      rw [hp2] at this
      norm_num at this
      norm_cast at this

  · intro hn
    cases hn with
    | inl hn1 =>
      -- when $n=0$, by subsituting directly into the original expression, we get $p = 5$
      rw [hn1]; norm_num
      apply And.intro
      positivity
      apply And.intro
      rw [hsqrt625, hsqrt4, sqrt_sq, sqrt_sq]
      positivity
      positivity
      rw [hsqrt625, hsqrt4, sqrt_sq, sqrt_sq]
      simp
      use 5
      rw [hsqrt25]
      simp
      positivity
      positivity
    | inr hn2 =>
      -- when $n = 144$, by subsituting directly into the original expression, we get $p = 7$
      rw [hn2]; norm_num
      apply And.intro
      positivity
      apply And.intro
      rw [hsqrt49, hsqrt4, sqrt_sq, sqrt_sq]
      linarith
      positivity
      positivity
      rw [hsqrt49, hsqrt4, sqrt_sq, sqrt_sq]
      norm_num
      rw [hsqrt16, hsqrt9, sqrt_sq, sqrt_sq]
      use 7
      norm_num
      repeat positivity
