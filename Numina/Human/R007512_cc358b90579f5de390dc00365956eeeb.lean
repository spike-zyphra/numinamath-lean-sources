import Mathlib

/- The sequence $\{a_n\}$ is defined by $$
a_0 = 1,a_1 = 1, \text{ and } a_n = a_{n - 1} + \frac {a_{n - 1}^2}{a_{n - 2}}\text{ for }n\ge2.
$$The sequence $\{b_n\}$ is defined by $$
b_0 = 1,b_1 = 3, \text{ and } b_n = b_{n - 1} + \frac {b_{n - 1}^2}{b_{n - 2}}\text{ for }n\ge2.$$Find $\frac {b_{32}}{a_{32}}$. -/
theorem algebra_22343 {a b : ℕ → ℝ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = a (n - 1) + (a (n - 1))^2 / a (n - 2))
    (hb0 : b 0 = 1) (hb1 : b 1 = 3)
    (hbn : ∀ n ≥ 2, b n = b (n - 1) + (b (n - 1))^2 / b (n - 2)) :
    b 32 / a 32 = 561 := by
  -- we prove that $a_n = n!$ by two step induction on $n$
  have aeq n : a n = Nat.factorial n := by
    let P : ℕ → Prop := by
      intro m
      exact (a m = Nat.factorial m)
    have H1 : P 0 := by
      simp only [ha0, Nat.factorial_zero, Nat.cast_one, P]
    have H2 : P 1 := by
      simp only [ha1, Nat.factorial_one, Nat.cast_one, P]
    have H3 : ((m : ℕ) → P m → P (Nat.succ m) → P (Nat.succ (Nat.succ m))) := by
      intro m Pm Pms
      simp only [P] at Pm
      simp only [Nat.succ_eq_add_one, P] at Pms
      simp only [Nat.succ_eq_add_one, P]
      rw [han _ (by exact Nat.le_add_left 2 m)]
      simp only [add_tsub_cancel_right, Pms, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.reduceSubDiff, Pm]
      rw [pow_two, mul_div_assoc, mul_div_cancel_right₀]
      ring
      by_contra contra
      have eq : (m.factorial : ℝ) = (0 : ℕ) := by
        rw [contra]
        exact Eq.symm AddMonoidWithOne.natCast_zero
      apply Nat.cast_injective at eq
      have : m.factorial ≠ 0 := by
        exact Nat.factorial_ne_zero m
      contradiction
    apply Nat.twoStepInduction H1 H2 H3 n
  -- we prove that $b_n = (n + 2)! / 2$ by two step induction on $n$
  have beq n : b n = Nat.factorial (n + 2) / 2 := by
    let P : ℕ → Prop := by
      intro m
      exact (b m = Nat.factorial (m + 2) / 2)
    have H1 : P 0 := by 
      simp only [hb0, Nat.cast_one, P]
      norm_num
    have H2 : P 1 := by
      simp only [hb1, Nat.reduceAdd, P, Nat.factorial_succ]
      norm_num
    have H3 : ((m : ℕ) → P m → P (Nat.succ m) → P (Nat.succ (Nat.succ m))) := by
      intro m Pm Pms
      simp only [P] at Pm
      simp only [Nat.succ_eq_add_one, P] at Pms
      simp only [Nat.succ_eq_add_one, P]
      rw [hbn _ (by exact Nat.le_add_left 2 m)]
      simp only [add_tsub_cancel_right, Pms, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.reduceSubDiff, Pm, pow_two]
      nth_rw 2 [mul_div_assoc]
      nth_rw 3 [mul_div_assoc]
      rw [mul_div_cancel_right₀]
      ring
      by_contra contra
      simp only [div_eq_zero_iff, mul_eq_zero, Nat.cast_eq_zero, OfNat.ofNat_ne_zero, or_false] at contra
      have : @Nat.cast ℝ AddMonoidWithOne.toNatCast m ≥ 0 := by
        exact Nat.cast_nonneg' m
      rcases contra with contra | contra | contra
      -- $m + 1 + 1 \neq 0$
      apply eq_sub_of_add_eq at contra
      apply eq_sub_of_add_eq at contra
      rw [contra] at this
      norm_num at this
      -- $m + 1 \neq 0$
      apply eq_sub_of_add_eq at contra
      rw [contra] at this
      norm_num at this
      -- $m! \neq 0$
      have : m.factorial ≠ 0 := by
        exact Nat.factorial_ne_zero m
      contradiction
    apply Nat.twoStepInduction H1 H2 H3 n
  -- so $b_32 / a_32 = 561$
  rw [aeq, beq, Nat.factorial_succ, Nat.factorial_succ]
  simp only [Nat.reduceAdd, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  ring_nf
  rw [mul_inv_cancel₀, one_mul]
  by_contra contra
  simp only [Nat.cast_eq_zero] at contra
  contradiction