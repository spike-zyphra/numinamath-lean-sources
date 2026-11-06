import Mathlib

/- The number r can be expressed as a four-place decimal 0.abcd, where a,b,c, and d represent digits, any of which could be zero. It is desired to approximate r by a fraction whose numerator is 1 or 2 and whose denominator is an integer. The closest such fraction to r is 2/7​. What is the number of possible values for r? -/
theorem number_theory_96824 : Set.ncard {r : ℝ | ∃ n : ℕ, n < 10000 ∧ r = n / 10000 ∧
    ∀ q : ℚ, q.num = 1 ∨ q.num = 2 → |r - 2 / 7| ≤ |r - q|} = 417 := by
  -- prove that if a < b and x < (a + b) / 2 then x is closer to a than to b: |x - a| < |x - b|
  have dist_left {a b x : ℝ} (hab : a < b) (hx : x < (a + b) / 2) : |x - a| < |x - b| := by
    cases' le_or_gt (x - a) 0 with h1 h1 <;> cases' le_or_gt (x - b) 0 with h2 h2 <;>
      [rw [abs_of_nonpos h1, abs_of_nonpos h2]; rw [abs_of_nonpos h1, abs_of_pos h2];
       rw [abs_of_pos h1, abs_of_nonpos h2]; rw [abs_of_pos h1, abs_of_pos h2]] <;>
      linarith
  -- prove that if a < b and x > (a + b) / 2 then x is closer to b than to a: |x - b| < |x - a|
  have dist_right {a b x : ℝ} (hab : a < b) (hx : x > (a + b) / 2) : |x - b| < |x - a| := by
    cases' le_or_gt (x - a) 0 with h1 h1 <;> cases' le_or_gt (x - b) 0 with h2 h2 <;>
      [rw [abs_of_nonpos h1, abs_of_nonpos h2]; rw [abs_of_nonpos h1, abs_of_pos h2];
       rw [abs_of_pos h1, abs_of_nonpos h2]; rw [abs_of_pos h1, abs_of_pos h2]] <;>
      linarith
  set s := {r | _}
  -- we are going to show that the set from the theorem statement is equal to
  -- an injective image of the interval of natural numbers [2679, 3095]
  suffices h : s = (fun (n : ℕ) => (n : ℝ) / 10000) '' Set.Icc (2679 : ℕ) 3095 by
    -- the main result follows from the theorem Set.ncard_image_of_injOn
    -- and the fact that fun (n : ℕ) => (n : ℝ) / 10000 is injective
    rw [h, Set.ncard_image_of_injOn]
    · simp [Set.ncard_eq_toFinset_card']
    simp only [Set.InjOn, Set.mem_Icc, and_imp]
    intro a ha1 ha2 b hb1 hb2
    field_simp
  ext r; simp [s]
  constructor
  -- show that r = n / 10000 and |r - 2 / 7| ≤ |r - q| for all rationals with numerators 1 or 2
  -- implies that n ∈ [2679, 3095]
  · rintro ⟨n, hn, hr, hq⟩
    use n
    simp [hr]
    constructor
    -- show that 2679 ≤ n
    · contrapose! hq
      -- assume that n < 2679 and show that 1 / 4 is closer to n / 10000 than 2 / 7
      use 1 / 4
      simp [hr]
      -- apply the auxiliary lemma dist_left with a = 1 / 4 < 2 / 7 = b
      apply dist_left (by norm_num)
      -- it is left to prove that n / 10000 < (1 / 4 + 2 / 7) / 2
      have : n ≤ 2678 := by omega
      rify at this
      linarith
    -- show that n ≤ 3095
    · contrapose! hq
      -- assume that 3095 < n and show that 1 / 3 is closer to n / 10000 than 2 / 7
      use 1 / 3
      simp [hr]
      -- apply the auxiliary lemma dist_right with a = 2 / 7 < 1 / 3 = b
      apply dist_right (by norm_num)
      -- it is left to prove that n / 10000 > (2 / 7 + 1 / 3) / 2
      have : 3096 ≤ n := by omega
      rify at this
      linarith
  -- show that 2679 ≤ n ≤ 3095 implies that |r - 2 / 7| ≤ |r - q| with r = n / 10000
  -- for any rational q with q.num = 1 or q.num = 2
  · rintro ⟨n, hn, hr_eq⟩
    use n
    simp only [hr_eq, true_and]
    refine ⟨by omega, ?_⟩
    -- fix a rational number q
    intro q hq_num
    have hr1 : 2679 / 10000 ≤ r := by rify at hn; linarith
    have hr2 : r ≤ 3095 / 10000 := by rify at hn; linarith
    -- consider two cases: q ≤ 1 / 4 and q > 1 / 4
    cases' le_or_gt q (1 / 4) with hq1 hq1
    -- if q ≤ 1 / 4 then we have the following chain of inequalities:
    -- |r - 2 / 7| < |r - 1 / 4| ≤ |r - 1 / 4| + |1 / 4 - q| = r - 1 / 4 + 1 / 4 - q = |r - q|
    · calc _ ≤ |r - 1 / 4| := by
                -- the first inequality follows from the lemma dist_right
                -- and the fact that r > (1 / 4 + 2 / 7) / 2
                apply le_of_lt
                apply dist_right (by norm_num)
                exact lt_of_lt_of_le (by norm_num) hr1
           _ ≤ |r - 1 / 4| + |1 / 4 - q| := by
                -- the second inequality follows from the fact 0 ≤ |1 / 4 - q|
                apply le_add_of_nonneg_right
                norm_cast
                exact abs_nonneg _
           _ = |r - q| := by
                -- the last equality is derived from q ≤ 1 / 4 ≤ r
                push_cast; rify at hq1
                rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
                rw [abs_of_nonneg (by linarith)]
                ring
    -- now we have q > 1 / 4
    -- consider two cases: 1 / 3 ≤ q and q < 1 / 3
    cases' le_or_gt (1 / 3) q with hq2 hq2
    -- if 1 / 3 ≤ q then we have the following chain of inequalities:
    -- |r - 2 / 7| < |r - 1 / 3| ≤ |1 / 3 - r| + |q - 1 / 3| = 1 / 3 - r + q - 1 / 3 = |r - q|
    · calc _ ≤ |r - 1 / 3| := by
                -- the first inequality follows from the lemma dist_left
                -- and the fact that r < (2 / 7 + 1 / 3) / 2
                apply le_of_lt
                apply dist_left (by norm_num)
                exact lt_of_le_of_lt hr2 (by norm_num)
           _ ≤ |1 / 3 - r| + |q - 1 / 3| := by
                -- the second inequality follows from the fact 0 ≤ |q - 1 / 3|
                rw [abs_sub_comm]
                apply le_add_of_nonneg_right
                norm_cast
                exact abs_nonneg _
           _ = |r - q| := by
                -- the last equality is derived from r ≤ 1 / 3 ≤ q
                push_cast; rify at hq2
                rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
                rw [abs_sub_comm, abs_of_nonneg (by linarith)]
                ring
    -- now we have 1 / 3 < q < 1 / 4
    -- show that q = 2 / 7 is the only rational numbers in the interval
    -- (1 / 3, 1 / 4) with q.num = 1 or q.num = 2
    suffices q = 2 / 7 by rw [this]; push_cast; exact le_refl _
    rw [←Rat.num_div_den q] at hq1 hq2 ⊢
    have hden_pos : 0 < (q.den : ℚ) := by
      norm_num
      have := q.den_nz
      omega
    -- q < 1 / 4 is equivalent to q.den < 4 * q.num
    replace hq1 : q.den < 4 * q.num := by
      norm_num at hq1
      rw [div_lt_div_iff₀ (by norm_num) hden_pos, one_mul, mul_comm] at hq1
      qify
      exact hq1
    -- 1 / 3 < q is equivalent to 3 * q.num < q.den
    replace hq2 : 3 * q.num < q.den := by
      norm_num at hq2
      rw [div_lt_div_iff₀ hden_pos (by norm_num), one_mul, mul_comm] at hq2
      qify
      exact hq2
    cases' hq_num with h h
    -- if q.num = 1 then 3 < q.den < 4. This case is impossible because q.den ∈ ℕ
    · omega
    -- if q.num = 2 then 6 < q.den < 8. The only possible solution is q.den = 7
    · rw [h] at hq1 hq2
      suffices q.den = 7 by rw [this, h]; norm_num
      omega