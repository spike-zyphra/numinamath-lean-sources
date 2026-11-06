import Mathlib


/- a+b, a-b are both odd or both even -/
lemma l_parity_add_sub (a b: ℤ):
  (Odd (a+b) ∧ Odd (a-b)) ∨ (Even (a+b) ∧ Even (a-b)) := by
  simp only [Int.odd_add, Int.odd_sub, and_self,
  Int.even_add, Int.even_sub]
  have h1 := Int.even_or_odd a
  have h2 := @Int.not_even_iff_odd a
  tauto

/- (-1)^(a+b) = (-1)^(a-b)  -/
lemma l_neg_one_pow_add_eq_sub {a b: ℤ}:
  (-1:ℝ)^(a+b) = (-1:ℝ)^(a-b) := by
  rcases (l_parity_add_sub a b) with ⟨h1,h2⟩  | ⟨h1,h2⟩
  <;> simp [h1.neg_one_zpow, h2.neg_one_zpow]


/- 24. S2 (POL) ${ }^{\text {IMO4 }}$ The positive real numbers $x_{0}, x_{1}, \ldots, x_{1995}$ satisfy $x_{0}=$ $x_{1995}$ and  $$ x_{i-1}+\frac{2}{x_{i-1}}=2 x_{i}+\frac{1}{x_{i}} $$  for $i=1,2, \ldots, 1995$. Find the maximum value that $x_{0}$ can have. -/
theorem algebra_24629 :
  IsGreatest {x0 : ℝ | ∃ x : ℕ → ℝ, x0 = x 0 ∧ x 0 = x 1995 ∧
    (∀ i ∈ Finset.range 1996, 0 < x i) ∧
    (∀i ∈ Finset.range 1995, x i  + 2 / x i = 2 * x (i + 1) + 1 / x (i+ 1))} (2 ^ 997) := by

  -- rewrite the given equation
  have hx_iff{x : ℕ → ℝ} (xpos: ∀ i ∈ Finset.range 1996 , 0 < x i):
    (∀i ∈ Finset.range 1995, x i + 2 / x i = 2 * x (i + 1) + 1 / x (i + 1)) ↔
    (∀i ∈ Finset.range 1995,(2 * x (i + 1) - x i) * (x (i + 1) * x i - 1) = 0) := by
    have h1: ∀i ∈ Finset.range 1995, i ∈ Finset.range 1996 := by
      intro i
      simp only [Finset.mem_range]
      intro hi; linarith only [hi]
    have h2: ∀i ∈ Finset.range 1995, i+1 ∈ Finset.range 1996 := by
      intro i
      simp only [Finset.mem_range]
      exact fun h => Nat.add_lt_of_lt_sub h
    constructor
    all_goals
      intro hx
      intro i hi
      specialize hx i hi
      have h3 := xpos i (h1 i hi)
      have h4 := xpos (i+1) (h2 i hi)
    · field_simp [h3.ne', h4.ne'] at hx
      linarith only [hx]
    · field_simp [h3.ne', h4.ne']
      linarith only [hx]

  -- if that condition holds, we claim x is of the form 2^k x0^(n-k)
  have xeq {n: ℕ} (hn: n < 1996) {x: ℕ → ℝ}
    (xpos: ∀ i ∈ Finset.range 1996, 0 < x i)
    (hx: ∀i ∈ Finset.range 1995, (2 * x (i + 1) - x i) * (x (i + 1) * x i - 1) = 0):
    ∃ (k:ℤ), |k| ≤ n ∧ x n = 2^k * (x 0)^((-1:ℤ)^(n-k): ℝ) := by
    induction' n with n ih
    · use 0
      simp
    · specialize ih (Nat.lt_of_succ_lt hn)
      rcases ih with ⟨k, klen, hxn⟩
      replace hn: n ∈ Finset.range 1995 := by
        simp only [Finset.mem_range]
        exact Nat.succ_lt_succ_iff.mp hn
      specialize hx n hn
      rcases (mul_eq_zero.mp hx) with hx | hx
      · replace hx: x (n+1) = x n / 2 := by linarith only [hx]
        use (k-1)
        constructor
        · apply (abs_sub k 1).trans ?_
          simp [klen]
        · have h1: ↑((n+1: ℕ):ℤ) - (k - 1) = (n - k) + 2 := by
            push_cast
            ring
          have h2: (2:ℝ)^(k-1) = 2^k / 2 := by
            rw [← Real.rpow_intCast, ← Real.rpow_intCast]
            push_cast
            rw [Real.rpow_sub (by norm_num)]
            simp
          rw [h1]; push_cast
          rw [← Int.cast_negOnePow, Int.negOnePow_add]
          push_cast
          simp only [Int.cast_negOnePow]
          rw [hx, hxn, h2]
          ring_nf
      · replace hx: x (n+1) = 1 / x n := by
          have: 0 < x n := by
            apply xpos n
            simp only [Finset.mem_range] at hn ⊢
            exact Nat.lt_succ_of_lt hn
          field_simp [this.ne']
          linarith only [hx]
        use (-k)
        constructor
        · rw [abs_neg]
          push_cast
          linarith only [klen]
        · rw [hxn] at hx
          simp only [Int.reduceNeg, Int.cast_neg,
          Int.cast_one, one_div, mul_inv_rev] at hx
          rw [hx]
          simp only [zpow_neg, Int.reduceNeg, Int.cast_neg, Int.cast_one,
          Nat.cast_add, Nat.cast_one, sub_neg_eq_add,
          mul_comm, mul_eq_mul_right_iff, inv_eq_zero]
          left
          have: (-1:ℝ)^(n+1+k:ℤ) = - (-1:ℝ)^(n-k:ℤ) := by
            rw [← l_neg_one_pow_add_eq_sub, add_comm (n+1:ℤ) k,
            ← add_assoc, ← Real.rpow_intCast]
            push_cast
            rw [Real.rpow_add_one (by norm_num)]
            simp only [mul_neg, mul_one, neg_inj, ← Real.rpow_intCast]
            push_cast
            rw [add_comm]
          rw [this, Real.rpow_neg (xpos 0 (by simp)).le]

  -- then we can express x_1995 in terms of x0
  have x1995 {x: ℕ → ℝ}
    (xpos: ∀ i ∈ Finset.range 1996, 0 < x i)
    (hx: ∀i ∈ Finset.range 1995, (2 * x (i + 1) - x i) * (x (i + 1) * x i - 1) = 0):
    ∃ (k:ℤ), |k| ≤ 1995 ∧ x 1995 = 2^k * (x 0)^((-1:ℤ)^(1995-k): ℝ) := by
    exact xeq (by norm_num) xpos hx

  constructor
  · -- verification x0 can reach 2^997
    -- a possible x is 2^997, 2^996, ..., 1, 1/2,1/4,...,1/2^997, 2^997
    set x: ℕ → ℝ := fun n =>
      if (n ≤ 997) then 2^(997 - n) else if (n < 1995) then (1 / 2^(n-997)) else 2^997 with x_def
    simp only [Set.mem_setOf_eq]
    use x
    have xpos: ∀ i ∈ Finset.range 1996, 0 < x i := by
      intro i _
      by_cases hi: i ≤ 997
      · simp only [x_def, if_pos hi, Nat.ofNat_pos, pow_pos]
      · simp only [x_def, one_div, hi, ↓reduceIte]
        by_cases hhi: i < 1995
        · simp only [hhi, ↓reduceIte, inv_pos, Nat.ofNat_pos, pow_pos]
        · simp only [hhi, ↓reduceIte, Nat.ofNat_pos, pow_pos]
    split_ands
    · simp only [x_def, zero_le, ↓reduceIte, tsub_zero]
    · simp only [x_def, one_div, zero_le, ↓reduceIte, tsub_zero,
      Nat.reduceLeDiff, lt_self_iff_false]
    · exact xpos
    · rw [hx_iff xpos]
      intro i ilt
      by_cases hi: i ≤ 997
      · by_cases ieq: i = 997
        · simp only [x_def, one_div, ieq, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceIte,
          Nat.reduceLT, Nat.reduceSub, pow_one, isUnit_iff_ne_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel,
          le_refl, tsub_self, pow_zero, sub_self, mul_one, zero_mul]
        · have hi': i+1 ≤ 997 := by
            change i < 997
            apply lt_of_le_of_ne hi ieq
          suffices 2 * x (i+1) - x i = 0 by
            simp only [this, zero_mul]
          simp only [x_def, hi', ↓reduceIte, Nat.reduceSubDiff, hi]
          rw [← pow_succ']
          apply sub_eq_zero_of_eq
          congr 1
          replace hi': i ≤ 996 := Nat.le_of_lt_succ hi'
          rw [add_comm _ 1, ← Nat.add_sub_assoc hi']
      · simp only [Finset.mem_range] at ilt
        have hi': ¬ i+1 ≤ 997 := by
          push_neg at hi ⊢
          apply lt_trans hi (by simp)
        by_cases ieq: i = 1994
        · simp only [mul_eq_zero]; right
          simp only [x_def, one_div, ieq, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceIte,
            lt_self_iff_false, Nat.lt_add_one, Nat.reduceSub, isUnit_iff_ne_zero, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, IsUnit.mul_inv_cancel,
            sub_self]
        · have ilt': i+1 < 1995 := by
            suffices i < 1994 by
              exact Nat.add_lt_of_lt_sub this
            replace ilt: i ≤ 1994 := Nat.le_of_lt_succ ilt
            apply lt_of_le_of_ne ilt ieq
          simp only [x_def, hi', ↓reduceIte, ilt',
          Nat.reduceSubDiff, hi, ilt, mul_eq_zero]
          left
          simp only [← one_div_pow]
          have: i - 996 = (i - 997) + 1 := by
            push_neg at hi
            zify
            rw [Nat.cast_sub (by omega), Nat.cast_sub hi.le]
            ring
          rw [this, pow_succ]
          ring

  · -- prove x0 ≤ 2^997
    rw [upperBounds]
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro _ x rfl x0eq xpos hx
    rw [hx_iff xpos] at hx
    specialize x1995 xpos hx
    rcases x1995 with ⟨k, kle, x1995⟩
    rw [← x0eq] at x1995
    push_cast at x1995

    -- here we obtain x0 = 2^k x0 ^ ( (-1)^(1995-k) )
    -- clearly that -1 power cannot be 1, otherwise 2^k = 1, k = 0
    -- therefore 1995 - k is odd, contradiction.
    have: Odd (1995 - k) := by
      by_contra!
      rw [Int.not_odd_iff_even] at this
      rw [this.neg_one_zpow] at x1995
      have h1 := xpos 0 (by simp)
      simp only [Real.rpow_one, ne_eq, h1.ne',
      not_false_eq_true, right_eq_mul₀] at x1995
      replace x1995: k = 0 := by
        rwa [zpow_eq_one_iff_right₀] at x1995
        <;> norm_num
      rw [x1995] at this
      absurd this
      exact Int.not_even_iff.mpr rfl
    rw [this.neg_one_zpow] at x1995
    have h1: Even k := by
      rw [Int.odd_sub] at this
      rw [← this]
      exact Int.odd_iff.mpr rfl

    -- then we have x0^2 = 2^k
    -- and 1995 - k odd, k ≤ 1994, x0 ≤ 2^(k/2) = 2^997
    replace x1995: x 0 = 2^(k/2) := by
      have h2 := xpos 0 (by simp)
      rw [Real.rpow_neg h2.le] at x1995
      field_simp [h2.ne'] at x1995
      rcases (even_iff_exists_two_mul.mp h1) with ⟨m, hm⟩
      rw [hm, two_mul, ← Real.rpow_intCast,
      Int.cast_add, Real.rpow_add (by norm_num),
      Real.rpow_intCast] at x1995
      simp only [hm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀]
      simp only [← pow_two] at x1995
      rwa [sq_eq_sq₀ h2.le] at x1995
      rw [← Real.rpow_intCast]
      apply Real.rpow_nonneg (by norm_num)
    have hk: k ≤ 1994 := by
      rw [abs_le] at kle
      suffices k ≠ 1995 by
        suffices k < 1995 by
          exact Int.lt_add_one_iff.mp this
        apply lt_of_le_of_ne kle.right this
      rintro keq
      rw [keq] at h1
      absurd h1
      exact Int.not_even_iff.mpr rfl
    have xle: (2:ℝ) ^ (k/2) ≤ (2:ℝ) ^ (997:ℝ) := by
      simp only [← Real.rpow_intCast, Nat.one_lt_ofNat,
      Real.rpow_le_rpow_left_iff]
      norm_cast
      apply Int.ediv_le_of_le_mul (by norm_num) ?_
      exact hk
    rw [x1995, ← Real.rpow_natCast]
    simpa only [Nat.cast_ofNat, ge_iff_le] using xle