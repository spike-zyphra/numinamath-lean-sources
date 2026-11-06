import Mathlib

open Filter

/- 7. [5] An infinite sequence of positive real numbers is defined by $a_{0}=1$ and $a_{n+2}=6 a_{n}-a_{n+1}$ for $n=0,1,2, \cdots$ Find the possible value(s) of $a_{2007}$. -/

-- lemma that proves sequence is A * 2^n + B * (-3)^n using induction, due to a(1)> 0, A > 0
lemma l_seq_term {a : ℕ → ℝ} (h : a 0 = 1) (h' : 0 < a 1) (h'' : ∀ n, a (n + 2) = 6 * a n - a (n + 1)) :
  ∃ (A B : ℝ), 0 < A ∧ ∀ n, a n = A * 2 ^ n + B * (-3) ^ n := by
  use (3 + a 1) / 5, (2 - a 1) / 5
  and_intros
  . positivity
  . rintro n
    induction' n using Nat.strong_induction_on with m hm
    match m with
    | 0 => ring_nf; assumption
    | 1 => ring_nf
    | k + 2 =>
      specialize h'' k
      rw [hm k (by linarith), hm (k + 1) (by linarith)] at h''
      rw [h'']
      ring

--if A * 2^n + B (-3) ^ n > 0 always with positive A and nonzero B, then there is positive C, such that C * 9 ^ n < 4 ^ n, this will help us create contradiction, we get the reuslt by using odd n or even n
lemma l_two_pow_add_three_pow_ineq {A B : ℝ} (ha : 0 < A) (hb : B ≠ 0) (h : ∀ (n : ℕ), 0 < A * 2 ^ n + B * (-3) ^ n) :
    ∃ (C : ℝ), 0 < C ∧ ∀ n, C * 9 ^ n < 4 ^ n  := by
  obtain hB | hB := lt_or_gt_of_ne hb
  . use - B / A
    and_intros
    . have : 0 < -B := by linarith
      positivity
    . rintro n
      specialize h (2 * n)
      rw [pow_mul, pow_mul] at h
      ring_nf at h
      rw [div_mul_eq_mul_div, div_lt_iff₀ ha]
      linarith
  . use 3 * B / (2 * A)
    and_intros
    . positivity
    . rintro n
      specialize h (2 * n + 1)
      rw [pow_succ, pow_succ, pow_mul, pow_mul] at h
      ring_nf at h
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith

-- 4^n = o(9^n) so eventually 4^n ≤ C * 9^n for any positive C
lemma l_four_pow_little_o_nine_pow {C : ℝ} (h : 0 < C) : ∃ k, ∀ n, k ≤ n → (4 : ℝ) ^ n ≤ C * 9 ^ n := by
  have h_little_oh := isLittleO_pow_pow_of_lt_left (show 0 ≤ (4 : ℝ) by norm_num) (show (4 : ℝ) < 9 by norm_num)
  rw [Asymptotics.isLittleO_iff] at h_little_oh
  specialize h_little_oh h
  simpa using h_little_oh

theorem algebra_151763 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h1 : a 0 = 1) (h2 : ∀ n, a (n + 2) = 6 * a n - a (n + 1)) :
    a 2007 = 2 ^ 2007 := by
  -- get general term using lemma
  obtain ⟨A, B, hA, hAB⟩ := l_seq_term h1 (ha 1) h2
  -- we'll prove B = 0, then A = 1 by a(0) = 1 and a(n) = 2^n
  suffices B = 0 by
    rw [this] at hAB
    simp at hAB
    have hA : A = 1 := by
      specialize hAB 0
      rw [h1] at hAB
      simpa using hAB.symm
    rw [hA] at hAB
    specialize hAB 2007
    simpa using hAB
  simp_rw [hAB] at ha
  -- assume B ≠ 0
  by_contra hB
  -- then we get 0 < C with C * 9^n < 4^n for all n
  obtain ⟨C, hC, h⟩ := l_two_pow_add_three_pow_ineq hA hB ha
  -- but eventually 4^n ≤ C * 9^n, so contradiction
  obtain ⟨k, h'⟩ := l_four_pow_little_o_nine_pow hC
  specialize h' k (by simp)
  specialize h k
  linarith