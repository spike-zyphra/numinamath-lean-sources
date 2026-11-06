import Mathlib

/-
Gegeven is een positief geheel getal $n$. Bepaal alle positieve reële getallen $x$ met

$$
n x^{2}+\frac{2^{2}}{x+1}+\frac{3^{2}}{x+2}+\ldots+\frac{(n+1)^{2}}{x+n}=n x+\frac{n(n+3)}{2} .
$$-/
theorem algebra_606204 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
  n * x ^ 2 + ∑ i ∈ Finset.range n, (i + 2) ^ 2 / (x + 1 + i) = n * x + n * (n + 3) / 2 ↔
  x = 1 := by
  constructor
  . intro h
    -- Rearrange the summation term, transforming it into an arithmetic sequence plus a term containing division.
    have t1 (i: ℕ) (_: i ∈ Finset.range n): (i + 2) ^ 2 / (x + 1 + i) = (i + 2) + (i + 2) / (x+ i + 1) * (1 - x) :=
      calc _ = (i + 2) * (x + 1 + i) / (x + 1 + i) + (i + 2) * (1 - x) / (x + 1 + i) := by ring_nf
           _ = (i + 2) + (i + 2) / (x + i + 1) * (1 - x) := by rw [mul_div_cancel_right₀]; ring_nf; linarith
    -- Find the sum of the arithmetic sequence.
    rw [
      Finset.sum_congr rfl t1,
      Finset.sum_add_distrib,
      Finset.sum_add_distrib,
      Finset.sum_eq_card_nsmul (show ∀ i ∈ Finset.range n, (2:ℝ) = (2) by intros; rfl),
      <-Nat.cast_sum,
      Finset.sum_range_id,
      Nat.cast_div (Even.two_dvd (Nat.even_mul_pred_self n)) (by simp),
      Nat.cast_mul,
      Nat.cast_sub (by linarith),
      <-add_assoc,
      <-Finset.sum_mul
    ] at h
    simp at h
    -- The sum of the arithmetic sequence exactly cancels out with the expression on the right-hand side.
    rw [show (n:ℝ) * (n - 1) / 2 + n * 2 = n * (n + 3) / 2 by ring, <-sub_eq_zero] at h
    let sum' := ∑ i ∈ Finset.range n, (i + 2) / (x + i + 1)
    have hsum' : ∑ i ∈ Finset.range n, (i + 2) / (x + i + 1) = sum' := rfl
    rw [hsum'] at h
    ring_nf at h
    -- transform into $sum'(1 - x) = nx(1 - x) $
    replace h : sum' * (1 - x) = n * x * (1 - x) := by rw [<-sub_eq_zero, <-h]; ring_nf
    -- By contradiction, assume \( x \neq 1 \), and eliminate the \( 1 - x \) term from the equation above.
    by_contra x_ne_1
    have : 1 - x ≠ 0 := by rw [ne_eq, sub_eq_zero, <-ne_eq]; symm; exact x_ne_1
    simp [this] at h
    have range_non_empty : (Finset.range n).Nonempty := by simp; linarith
    -- Consider cases separately: \( x > 1 \) and \( x < 1 \).
    match lt_or_lt_iff_ne.2 x_ne_1 with
    | Or.inl x_lt_1 =>
      -- each term in the summation is greater than 1, so their sum exceeds \( nx \), making it impossible to equal \( nx \), leading to a contradiction.
      have : ∀ i ∈ Finset.range n, 1 < (i + 2) / (x + i + 1):= by
        intro i _
        rw [one_lt_div]
        linarith
        linarith
      have : n * x < sum' := by
        have h' := Finset.sum_lt_sum_of_nonempty range_non_empty this
        simp at h'
        apply lt_trans' h'
        simp [show 0 < (n:ℝ) by norm_cast]
        exact x_lt_1
      rw [h] at this
      simp only [lt_self_iff_false] at this
    | Or.inr x_gt_1 =>
      -- each term in the summation is less than 1, so their sum is less than \( nx \), making it impossible to equal \( nx \), leading to a contradiction.
      have : ∀ i ∈ Finset.range n, (i + 2) / (x + i + 1) < 1 := by
        intro i _
        rw [div_lt_one]
        linarith
        linarith
      have : sum' < n * x := by
        have h' := Finset.sum_lt_sum_of_nonempty range_non_empty this
        simp at h'
        apply lt_trans h'
        simp [show 0 < (n:ℝ) by norm_cast]
        exact x_gt_1
      rw [h] at this
      simp only [lt_self_iff_false] at this
  -- Prove that the condition holds when \( x = 1 \).
  . intro hx
    rw [hx, one_add_one_eq_two]
    simp
    -- Eliminate the squares and transform it into the summation of an arithmetic sequence.
    have t1 (i: ℕ) (_: i ∈ Finset.range n): (↑i + 2) ^ 2 / (2 + ↑i) = (i:ℝ) + 2 := by
      nth_rw 2 [add_comm]
      rw [sq, mul_div_cancel_right₀]
      norm_cast
    -- Find the sum of the arithmetic sequence.
    rw [
      Finset.sum_congr rfl t1,
      Finset.sum_add_distrib,
      Finset.sum_eq_card_nsmul (show ∀ i ∈ Finset.range n, (2:ℝ) = (2) by intros; rfl),
      <-Nat.cast_sum,
      Finset.sum_range_id,
      Nat.cast_div (Even.two_dvd (Nat.even_mul_pred_self n)) (by simp),
      Nat.cast_mul,
      Nat.cast_sub (by linarith),
    ]
    simp
    ring
