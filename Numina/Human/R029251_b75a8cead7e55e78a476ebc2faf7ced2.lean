import Mathlib

/- 1. A1 (USA) Let $a_{0}=1994$ and $a_{n+1}=\frac{a_{n}^{2}}{a_{n}+1}$ for each nonnegative integer $n$. Prove that $1994-n$ is the greatest integer less than or equal to $a_{n}$, $0 \leq n \leq 998$. -/
theorem algebra_24524 {a : ℕ → ℝ} (ha0 : a 0 = 1994)
    (han : ∀ n, a (n + 1) = (a n)^2 / (a n + 1)) :
    ∀ n ≤ 998, ⌊a n⌋ = 1994 - n := by

  -- Prove by induction that each number in the sequence is positive.
  have a_i_pos (n: ℕ) : 0 < a n := by
    induction' n with n ih
    · norm_num [ha0]
    · rw [han]
      apply div_pos
      exact sq_pos_of_pos ih
      linarith
  -- $1 / (a_n + 1)$ is positive
  have sum_item_pos (n: ℕ) : 0 < 1 / (a n + 1) := by
    rw [one_div]
    apply inv_pos_of_pos
    exact add_pos_of_nonneg_of_pos (le_of_lt <| a_i_pos n) zero_lt_one

  -- Since $a_{k}-a_{k+1}=1-\frac{1}{a_{k}+1}$, we have $a_{n}=a_{0}+\left(a_{1}-a_{0}\right)+\cdots+\left(a_{n}-a_{n-1}\right)=1994-n+\frac{1}{a_{0}+1}+\cdots+\frac{1}{a_{n-1}+1}$
  -- We prove it by induction.
  have a_i_sum (n: ℕ): a n = 1994 - n + ∑ i in Finset.range n, 1 / (a i + 1) := by
    induction n with
    | zero =>
      simp
      exact ha0
    | succ n' ih =>
      simp
      rw [Finset.sum_range_succ]
      simp at ih
      rw [
        calc ∑ x ∈ Finset.range (n'), (a x + 1)⁻¹ = (1994 - ↑n' + ∑ x ∈ Finset.range n', (a x + 1)⁻¹) - (1994 - ↑n') := by simp
        _ = a (n') - (1994 - ↑n') := by rw [ih]
      ]
      rw [han]
      ring_nf
      have h': 1 + a (n') ≠ 0 := by
        apply ne_of_gt
        apply add_pos
        norm_num
        apply a_i_pos
      rw [
        show (a n') ^ 2 = (a n' - 1) * (1 + a n') + 1 by ring_nf,
        add_mul,
        mul_assoc,
        IsUnit.mul_inv_cancel
      ]
      ring_nf
      simp only [isUnit_iff_ne_zero]
      linarith only [a_i_pos n']

  -- Prove that each term in the sequence is smaller than the previous one.
  have a_decrease' (n: ℕ) : a (n + 1) < a n := by
    -- Since both of them is postive, we prove $a_(n+1) < a_n$ by proving $a_(n+1) / a_n < 1$.
    have h' : a (n + 1) / a n < 1 := by
      rw [han]
      rw [
        calc a n ^ 2 / (a n + 1) / a n = (a n) * ((a n) / (a n + 1)  / (a n)) := by ring_nf
        _ = a n / (a n + 1) := by rw [mul_div_cancel₀ ]; linarith only [a_i_pos n]
        _ = (a n + 1) / (a n + 1) - 1 / (a n + 1) := by ring_nf
        _ = 1 - 1 / (a n + 1) := by rw [div_self]; linarith only [a_i_pos n]
      ]
      rw [sub_lt_self_iff]
      exact sum_item_pos _
    rw [div_lt_one] at h'
    exact h'
    exact a_i_pos n
    
  -- Prove that the sequence is decreasing.
  have a_decrease {n: ℕ} {m: ℕ} (h: n ≤ m) : a m ≤ a n := by
    let k := m - n
    have h': m = n + k := by simp only [k]; rw [add_comm]; symm; exact Nat.sub_add_cancel h
    rw [h']
    induction k with
    | zero => simp
    | succ k ih =>
      apply le_trans' ih
      rw [<-add_assoc]
      apply le_of_lt
      exact a_decrease' _
  -- prove $1994 - n ≤ a_n$ by ignoring the sum in `a_i_sum`.
  have h1 (n: ℕ): 1994 - n ≤ a n := by
    rw [a_i_sum]
    simp
    apply Finset.sum_nonneg
    intros i hi
    rw [<-one_div]
    exact le_of_lt (sum_item_pos _)

  -- when n is positive, $1994 - n < a_n$
  -- prove $1994 - n < a_n$ by proving the sum in `a_i_sum` is positive.
  have h2 (n: ℕ) (n_gt_0: 0 < n): 1994 - n < a n := by
    rw [a_i_sum]
    simp
    apply Finset.sum_pos
    intros i hi
    rw [<-one_div]
    exact (sum_item_pos _)
    simp
    linarith

  -- prove the floor of $a_n$ is $1994 - n$.
  intro n' hn'
  rw [Int.floor_eq_iff]
  constructor
  -- we need $1994 - n ≤ a_n$, which is proved by `h1`.
  . apply le_trans' (h1 n')
    apply le_of_eq
    norm_cast
  -- prove $a_n < (1994 - n) + 1$
  -- we expand the sum in `a_i_sum` and prove it is less than 1.
  . rw [a_i_sum]
    simp
    -- we need ∑ x ∈ Finset.range n', (a x + 1)⁻¹ < 1
    -- First, we replace n' with 998.
    have h3: ∑ i ∈ Finset.range n', (a i + 1)⁻¹ ≤ ∑ i ∈ Finset.range 998, 1 / (a i + 1) := by
      have h' := Finset.range_add n' (998 - n')
      have calc1 : n' + (998 - n') = 998 := by
        apply show (n' + (998 - n'): ℤ) = 998 → n' + (998 - n') = 998 by norm_cast; exact id
        ring_nf
      rw [calc1] at h'
      rw [h']
      rw [Finset.sum_union (Finset.disjoint_range_addLeftEmbedding n' _)]
      simp
      apply Finset.sum_nonneg
      intros i hi
      rw [<-one_div]
      exact le_of_lt (sum_item_pos _)
    -- And then we replace $a_i$ with $a_{997}$.
    have h4: ∑ i ∈ Finset.range 998, 1 / (a i + 1) ≤ ∑ i ∈ Finset.range 998, 1 / (a 997 + 1) := by
      apply Finset.sum_le_sum
      intros i hi
      apply one_div_le_one_div_of_le
      linarith [a_i_pos 997]
      simp
      apply a_decrease
      simp at hi
      linarith only [hi]
    -- Adding 998 items of $1 / (a 997 + 1)$ equals to $998 / (a 997 + 1)$
    have h5: ∑ i ∈ Finset.range 998, 1 / (a 997 + 1) = 998 / (a 997 + 1) := by
      rw [Finset.sum_eq_card_nsmul (show ∀ i ∈ Finset.range 998,1 / (a 997 + 1) = 1 / (a 997 + 1) by simp)]
      simp
      ring_nf
    -- Since $a_{997} > 997$ (proved by `h2`), we have $998 / (a_{997} + 1) < 1$.
    have h6: 998 / (a 997 + 1) < 1 := by
      have h' := h2 997 (by norm_num)
      ring_nf at h'
      rw [div_lt_iff₀]
      simp
      linarith
      linarith
    linarith
