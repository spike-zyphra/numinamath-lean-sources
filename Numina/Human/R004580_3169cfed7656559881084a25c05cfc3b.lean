import Mathlib
open Real

/- 14. Given a sequence $\left\{a_{n}\right\}$ with all terms being positive, the sum of the first $n$ terms is $S_{n}$, and $a_{n}+1=2 \sqrt{S_{n}}\left(n \in \mathbf{Z}_{+}\right)$.
(1) Find the general term formula for the sequence $\left\{a_{n}\right\}$;
(2) Let $b_{n}=\frac{a_{n+2}}{a_{n} a_{n+1} 2^{n}}$, the sum of the first $n$ terms of the sequence $b_{n}$ is $T_{n}$, prove: $\frac{5}{6} \leqslant T_{n}<1$. -/
theorem algebra_286339 {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (h : ∀ n, a n + 1 = 2 * √(∑ i ∈ Finset.range (n + 1), a i)) :
    (∀ n, a n = 2 * n + 1) ∧
    (∀ n, ∑ i ∈ Finset.range (n + 1), a (i + 2) / (a i * a (i + 1) * 2^(i + 1)) ∈ Set.Ico (5 / 6) 1) := by
  -- Find the first element of the sequence (base case for induction)
  have ha0 : a 0 = 1
  · have : √(a 0) - 1 = 0
    have := h 0
    simp only [zero_add, Finset.range_one, Finset.sum_singleton] at this
    · rw [←sq_eq_zero_iff, sub_sq, (ha_pos 0).le |> sq_sqrt]; linarith
    rcases sq_eq_one_iff.mp (show (√(a 0))^2 = 1 by nlinarith) with h' | h'
    · rw [←sq_sqrt (ha_pos 0).le]
      nlinarith
    · linarith [sqrt_nonneg (a 0)]
  -- Show that the sum is nonnegative: this is useful later
  have hz : ∀ n, ∑ i ∈ Finset.range n, a i ≥ 0
  · intro n
    exact Finset.sum_nonneg (fun m hm => (ha_pos m).le)
  -- Show by induction that √(S n) = n
  have hs : ∀ n, √(∑ i ∈ Finset.range n, a i) = n
  · intro n; induction' n using Nat.strong_induction_on with n ih
    match n with
    | 0 => simp only [Finset.range_zero, Finset.sum_empty, sqrt_zero, CharP.cast_eq_zero]
    | 1 => simp only [Finset.range_one, Finset.sum_singleton, ha0, sqrt_one, Nat.cast_one]
    | n + 1 + 1 =>
      symm
      rw [Nat.cast_add, Nat.cast_one, ←ih (n + 1), ←@add_right_cancel_iff _ _ _ (-1 : ℝ),
          add_neg_cancel_right, Real.sqrt_eq_iff_eq_sq (hz _), add_sq,
          sq_sqrt (hz _), ←h (n + 1), Finset.sum_range_succ _ (n + 1)]
      ring
      simp only [le_add_neg_iff_add_le, zero_add, one_le_sqrt]
      rw [Finset.sum_range_succ', ha0, le_add_iff_nonneg_left]
      exact Finset.sum_nonneg (fun k hk => (ha_pos (k + 1)).le)
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]
  -- Use this to get the general form of a n
  have ha : ∀ n, a n = 2 * n + 1
  · intro n
    rw [←@add_right_cancel_iff _ _ _ (1 : ℝ), h, hs, Nat.cast_add, Nat.cast_one]
    ring
  constructor
  · exact ha
  -- Now we prove the bounds on ∑ b i
  -- First show that the sum telescopes
  let f := fun (n : ℕ) => (1 : ℝ) / ((2 : ℝ)^(n : ℝ) * (2 * n + 1))
  have hb : ∀ n, a (n + 2) / (a n * a (n + 1) * 2^(n + 1)) = f n - f (n + 1)
  · intro n
    unfold f
    rw [ha (n + 2), ha (n + 1), ha n]
    field_simp
    move_mul [2 * (n : ℝ) + 1, 2 * ((n : ℝ) + 1) + 1]
    rw [mul_right_cancel_iff_of_pos (by positivity),
        mul_right_cancel_iff_of_pos (by positivity),
        show (2 : ℝ)^(n + 1) = 2^((n : ℝ) + 1) by norm_cast]
    move_mul [2 ^ ((n : ℝ) + 1)]
    rw [mul_right_cancel_iff_of_pos (by positivity),
        show (2 : ℝ)^((n : ℝ) + 1) = (2 : ℝ) * 2^n by exact_mod_cast Nat.pow_succ']
    ring
  intro n
  rw [Finset.sum_congr rfl (fun i hi => hb i), Finset.sum_range_sub']
  -- The lower bound follows from f being antitone and f 1 = 1/6
  constructor
  · have anti_f : Antitone f
    · apply antitone_nat_of_succ_le
      intro n
      unfold f
      rw [one_div, one_div]
      apply inv_anti₀ (by positivity)
      apply mul_le_mul
      · exact_mod_cast pow_le_pow_right₀ one_le_two (Nat.le_succ n)
      · push_cast
        linarith
      · linarith
      push_cast
      positivity
    have hf1 : f 1 = 1 / 6
    · unfold f
      norm_num
    have hfn := anti_f (Nat.le_add_left 1 n)
    rw [hf1] at hfn
    linarith
  -- The upper bound follows from f 0 = 2 and f (n + 1) > 0
  · unfold f
    norm_num
    apply mul_pos
    rw [inv_pos]
    linarith
    rw [inv_pos]
    apply rpow_pos_of_pos zero_lt_two