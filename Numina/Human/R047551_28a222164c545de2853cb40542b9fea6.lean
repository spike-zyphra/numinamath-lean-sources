import Mathlib

open Real Finset

/-
Given a sequence $a_1,$ $a_2,$ $a_3,$ $\dots,$ let $S_n$ denote the sum of the first $n$ terms of the sequence.
If $a_1 = 1$ and $a_n = \frac{2S_n^2}{2S_n - 1}$ for all $n \ge 2,$ then find $a_{100}.$
-/
theorem algebra_14190
    (a S : ℕ → ℝ)
    (hS : ∀ n, S n = ∑ i ∈ Icc 0 n, a i)
    (ha0 : a 0 = 1)
    (han : ∀ n ≥ 1, a n = (2 * (S n) ^ 2) / (2 * S n - 1)) :
    a 99 = - 2 / 39203 := by

  -- By definition of $S_n,$ we can write $a_n = S_n - S_{n - 1}.$ Then $S_n - S_{n - 1} = \frac{2S_n^2}{2S_n - 1},$​
  have r1 : ∀ n ≥ 1, S n - S (n - 1) = (2 * (S n) ^ 2) / (2 * S n - 1) := by
    intro n hn
    conv => lhs; rw [hS, hS, show n = n - 1 + 1 by omega, sum_Icc_succ_top (by omega), Nat.sub_add_cancel (by omega), add_sub_cancel_left]
    exact han n hn

  -- auxiliary lemmas

  have l1 : ∀ n, S n ≠ 0 := by
    intro n
    induction n with
    | zero =>
      simp [hS, ha0]
    | succ n ih =>
      by_contra! h_contra
      specialize r1 (n + 1) (Nat.le_add_left 1 n)
      simp [h_contra, ih] at r1

  have l2 : ∀ n, S n ≠ 1 / 2 := by
    intro n
    induction n with
    | zero =>
      simp [hS, ha0]
    | succ n ih =>
      by_contra! h_contra
      specialize r1 (n + 1) (by linarith)
      simp [h_contra] at r1
      rw [inv_eq_one_div] at r1
      exact ih (by linarith)

  -- so $(2S_n - 1)(S_n - S_{n - 1}) = 2S_n^2.$​
  have : ∀ n ≥ 1, (2 * S n - 1) * (S n - S (n - 1)) = 2 * (S n) ^ 2 := by
    simp_rw [mul_comm (2 * S _ - 1)]
    convert fun n hn => (eq_mul_inv_iff_mul_eq₀ ?_).mp (r1 n hn) using 1
    by_contra!
    exact l2 n (by linarith)

  -- This simplifies to $S_{n - 1} = 2S_{n - 1} S_n + S_n.$
  have : ∀ n ≥ 1, S (n - 1) = 2 * S (n - 1) * S n + S n  := by
    intro n hn
    linarith [this n hn]

  -- we conclude that all the $S_n$ are nonzero.  Thus, we can divide both sides by $S_{n - 1} S_n,$ to get $\frac{1}{S_n} = \frac{1}{S_{n - 1}} + 2.$
  have : ∀ n ≥ 1, (S n)⁻¹ = (S (n - 1))⁻¹ + 2 := by
    intro n hn
    specialize this n hn
    apply_fun fun t => t * (S n)⁻¹ * (S (n - 1))⁻¹ at this
    rw [mul_right_comm, mul_inv_cancel₀, one_mul,
        mul_assoc, add_mul, mul_comm 2, mul_comm, mul_assoc _ 2, mul_assoc (S n)⁻¹, ← mul_assoc (S (n - 1))⁻¹, inv_mul_cancel₀, one_mul, mul_comm, mul_assoc, mul_inv_cancel₀, mul_one, ← mul_assoc, mul_inv_cancel₀, one_mul, add_comm] at this
    any_goals apply l1
    exact this

  -- Since $\frac{1}{S_1} = 1,$ it follows that $\frac{1}{S_2} = 3,$ $\frac{1}{S_3} = 5,$ and so on.  In general, $\frac{1}{S_n} = 2n - 1,$
  have : ∀ n, (S n)⁻¹ = 2 * (n + 1) - 1 := by
    intro n
    induction n with
    | zero =>
      simp [hS, ha0, show (2:ℝ) - 1 = 1 by norm_num]
    | succ n ih =>
      rw [this (n + 1) (by linarith), Nat.add_sub_cancel, ih, Nat.cast_add]
      ring_nf

  -- Therefore, answer is $\boxed{-\frac{2}{39203}}.$
  rw [han 99 (by linarith), ← inv_inv (S 99), this 99]
  norm_num
