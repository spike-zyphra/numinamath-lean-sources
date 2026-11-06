import Mathlib

open Finset


theorem number_theory_77603 :
    ∑ i ∈ range 1989, (-1 : ℝ) ^ i * (1989 - i) / (i + 2) =
    ∑ i ∈ range 995, (2 * i + 1 : ℝ) / (996 + i) := by

  -- sublemma
  have l_1 (n : ℕ) : (2 * n) - (∑ i ∈ range (2 * n - 1), (-1 : ℝ) ^ i * ((2 * n - 1) - i) / (i + 2)) =
    (2 * n + 1) * (∑ i ∈ range (2 * n), (-1 : ℝ) ^ i * 1 / (i + 1)) := by
    rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
    . simp [hn_zero]

    have aux_1 (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, f (i + 1) = (∑ i ∈ range (n + 1), f i) - f 0 := by
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [sum_range_succ, ih, sum_range_succ _ (n + 1)]
        ring

    have aux_2 (n : ℕ) : 0 = ∑ i ∈ range (2 * n), (-1 : ℝ) ^ i := by
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        rw [mul_add, mul_one, sum_range_succ, sum_range_succ, ← ih, pow_add]
        ring

    specialize aux_1 (fun i => (-1 : ℝ) ^ (i + 1) * ((2 * n - 1) - (i - 1)) / (i + 1)) (2 * n - 1)
    have t1 : ∀ (x : ℝ), x + 1 + 1 = x + 2 := fun x => Mathlib.Tactic.Ring.add_pf_add_lt x one_add_one_eq_two
    have t2 : ∀ x, (-1 : ℝ) ^ (x + 1 + 1) = (-1 : ℝ) ^ x := by
      intro x
      rw [add_assoc, pow_add, neg_one_pow_two, mul_one]
    simp_rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, t1, t2] at aux_1
    rw [aux_1, Nat.sub_add_cancel (by omega),
        sub_eq_iff_eq_add,
        mul_sum, ← add_sub_assoc, ← sum_add_distrib]
    apply eq_sub_of_add_eq

    convert aux_2 n
    . ring
    . field_simp
      ring

  -- sublemma
  have l_2 (n : ℕ) : (2 * n) - (∑ i ∈ range n, (2 * i + 1 : ℝ) / (n + 1 + i)) =
      (2 * n + 1) * (∑ i ∈ range n, (1 : ℝ) / (n + 1 + i)) := by
    rw [sub_eq_iff_eq_add]
    rw [mul_sum, ← sum_add_distrib]
    trans ∑ i ∈ range n, 2
    . rw [sum_const, card_range]
      ring
    . rw [Finset.sum_congr rfl]
      intro i hi
      field_simp
      ring

  -- sublemma
  have l_3 (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, f (i + 1) = (∑ i ∈ range (n + 1), f i) - f 0 := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ _ (n + 1)]
      ring

  -- Generally, $1-\frac{1}{2}+\frac{1}{3}-\frac{1}{4}+....+\frac{1}{2n} = \frac{1}{n+1}+\frac{1}{n+2}+\frac{1}{n+3}+....+\frac{1}{2n}$ is seen to be true for positive integer $n$ by induction
  have l_4 (n : ℕ) : ∑ i ∈ range (2 * n), (-1 : ℝ) ^ i * 1 / (i + 1) =
      ∑ i ∈ range n, (1 : ℝ) / (n + 1 + i) := by

    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      conv => lhs; rw [mul_add, sum_range_succ, sum_range_succ, ih]
      symm
      calc
        _ = (∑ i ∈ range (n + 2), (1 : ℝ) / (n + 1 + i)) - (1 : ℝ) / (n + 1) := by
          specialize l_3 (fun t => (1 : ℝ) / (n + 1 + t)) (n + 1)
          convert l_3 using 3
          . norm_cast
            ring
          . norm_num
        _ = (∑ i ∈ range n, (1 : ℝ) / (n + 1 + i)) + (1 : ℝ) / (2 * n + 1) + (1 : ℝ) / (2 * n + 2) - (1 : ℝ) / (n + 1) := by
          rw [sum_range_succ, sum_range_succ]
          congr 3
          . congr 1
            ring
          . norm_cast
            ring
        _ = _ := by
          rw [add_sub_assoc]
          congr
          . simp
          . norm_cast
          . simp [pow_add, pow_mul, neg_one_pow_two]
            field_simp
            ring

  -- function $f(x) = \frac{1990 - x}{1991} is injective.$
  have h_inj : Function.Injective fun (t : ℝ) => (1990 - t) / 1991 := by
    apply Function.injective_iff_hasLeftInverse.mpr
    unfold Function.HasLeftInverse Function.LeftInverse
    use fun (t : ℝ) => -(t * 1991) + 1990
    simp

  -- Subtracting LHS from $1990$ and each term of the RHS from $2$ , and then dividing both sides by $1991$,
  apply_fun fun t => (1990 - t) / 1991

  -- LHS becomes $1-\frac{1}{2}+\frac{1}{3}-\frac{1}{4}+....-\frac{1}{1990} $
  have h1 : (1990 - (∑ i ∈ range 1989, (-1 : ℝ) ^ i * (1989 - i) / (i + 2))) / 1991 =
      ∑ i ∈ range 1990, (-1 : ℝ) ^ i * 1 / (i + 1) := by

    have : 1990 - (∑ i ∈ range 1989, (-1 : ℝ) ^ i * (1989 - i) / (i + 2)) =
        1991 * (∑ i ∈ range 1990, (-1 : ℝ) ^ i * 1 / (i + 1)) := by
      convert l_1 995
      <;> norm_num

    rw [this, mul_div_cancel_left₀ _ (by positivity)]

  -- RHS becomes $\frac{1}{996}+\frac{1}{997}+\frac{1}{998}+....+\frac{1}{1990}$
  have h2 : (1990 - (∑ i ∈ range 995, (2 * i + 1 : ℝ) / (996 + i))) / 1991 =
      ∑ i ∈ range 995, (1 : ℝ) / (996 + i) := by

    have : 1990 - (∑ i ∈ range 995, (2 * i + 1 : ℝ) / (996 + i)) =
        1991 * (∑ i ∈ range 995, (1 : ℝ) / (996 + i)) := by
      convert l_2 995
      <;> norm_num

    rw [this, mul_div_cancel_left₀ _ (by positivity)]

  -- then we're done
  dsimp only
  rw [h1, h2]
  have := l_4 995
  rw [show 2 * 995 = 1990 by ring,
      show ((995 : ℕ) : ℝ) + 1 = 996 by norm_num] at this
  exact this
