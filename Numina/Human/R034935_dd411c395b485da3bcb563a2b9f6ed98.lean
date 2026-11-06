import Mathlib
/-- Let $c>0$ be a given positive real and $\mathbb{R}_{>0}$ be the set of all positive reals. Find all functions $f: \mathbb{R}_{>0} \rightarrow \mathbb{R}_{>0}$ such that

$$
f((c+1) x+f(y))=f(x+2 y)+2 c x \quad \text { for all } x, y \in \mathbb{R}_{>0}
$$

Answer: $f(x)=2 x$ for all $x>0$. -/
theorem algebra_606322 (c : ℝ) (hc : 0 < c) (f : ℝ → ℝ) (hpos : ∀ x, 0 < x → 0 < f x) :
    (∀ x y, 0 < x → 0 < y → f ((c + 1) * x + f y) = f (x + 2 * y) + 2 * c * x) ↔
    ∀ x, 0 < x → f x = 2 * x := by

  constructor; intro h

  -- We first prove that $f(x) \geq 2 x$ for all $x > 0$.
  have hflb  : ∀ x, 0 < x → 2 * x ≤ f x := by

    -- Suppose, for the sake of contradiction, that $f(y) < 2 y$ for some $y > 0$.
    by_contra hlt; push_neg at hlt
    obtain ⟨y, hypos, hfy⟩ := hlt
    apply sub_pos.mpr at hfy

    -- Choose $x = \frac{2 y - f(y)}{c}$
    set x := (2 * y - f y) / c with hx
    have hxpos : 0 < x := div_pos hfy hc
    specialize h x y hxpos hypos

    -- Then $2 c x = 0$
    have h2cx : 2 * c * x = 0 := calc
      _ = f ((c + 1) * x + f y) - f (x + 2 * y) := by
        rw [h, add_sub_cancel_left]
      _ = f (x + c * x + f y) - f (x + 2 * y) := by
        rw [add_one_mul, add_comm (c * x)]
      _ = f (x + 2 * y) - f (x + 2 * y) := by
        nth_rw 2 [hx]
        rw [add_assoc, mul_comm, div_mul_cancel₀ (2 * y - f y) (show c ≠ 0 by positivity),
          sub_add_cancel]
      _ = 0 := by
        rw [sub_self]

    -- On the other hand $2 c x > 0$ and we get a contradiction
    have h2cx' : 0 < 2 * c * x := by positivity
    linarith only [h2cx, h2cx']

  -- Next, we show that $f(x) \leq 2 x$ for every $x > 0$.
  have hfub : ∀ x, 0 < x → f x ≤ 2 * x := by

    -- Suppose, for the sake of contradiction, that there exists $y > 0$ such that $f(y) > 2 y$.
    by_contra hgt; push_neg at hgt
    obtain ⟨y, hypos, hfy⟩ := hgt
    apply sub_pos.mpr at hfy

    -- Define a sequence $x_n = (x_0 + (f(y) - 2y)/c)(c+1)^n - (f(y) - 2y)/c$ for some $x_0 >0$
    let x (n : ℕ) := (1 + (f y - 2 * y) / c) * (c + 1) ^ n - (f y - 2 * y)/c

    -- This sequence satisfies $x_{n+1} = (c+1)x_n + f(y) - 2y$ and each $x_n$ is positive
    have hxsucc (n : ℕ) : x (n + 1) = (c + 1) * x n + f y - 2 * y := by
      induction' n with n ih
      · ring_nf
        simp only [add_left_inj, add_right_inj, mul_assoc, mul_inv_cancel₀ (Ne.symm (ne_of_lt hc)),
          mul_one, sub_right_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero]
      · calc
          _ = (1 + (f y - 2 * y)/c) * (c + 1) ^ (n + 1) * (c + 1) - (f y - 2 * y) / c := by
            ring
          _ = (c + 1) * (1 + (f y - 2 * y) / c) * (c + 1) ^ (n + 1)
              - (c + 1) * (f y - 2 * y) / c +  c * (f y - 2 * y) / c := by
            ring
          _ = (c + 1) * (1 + (f y - 2 * y) / c) * (c + 1) ^ (n + 1)
              - (c + 1) * (f y - 2 * y) / c + (f y - 2 * y) := by
            rw [mul_div_cancel_left₀]
            exact Ne.symm (ne_of_lt hc)
          _ = (c + 1) * x (n + 1) + f y - 2 * y := by
            ring
    have hxpos (n : ℕ) : 0 < x n := by
      induction' n with n ih
      · simp only [x, pow_zero, mul_one, add_sub_cancel_right, zero_lt_one]
      · rw [hxsucc, add_sub_assoc]
        exact add_pos (by positivity) hfy

    -- Let $a_n = x_n + 2y$ and note that $2y < a_n$
    let a (n : ℕ) := x n + 2 * y
    have hapos (n : ℕ) : 2 * y < a n := by
      simp only [a, lt_add_iff_pos_left]
      exact hxpos n

    -- Substituting $x_n$ into the main hypothesis we obtain $f(a_{n+1}) = f(a_n) + 2cx_n$
    have hfsucc (n : ℕ) : f (a (n + 1)) = f (a n) + 2 * c * (x n) := by
      rw [← h (x n) y (hxpos n) hypos]
      simp only [a, hxsucc, sub_add_cancel]

    -- Iterating the above, we show that $f(a_n) = f(a_0) + 2c\sum_{k=0}^{n-1} x_k$
    have hfsum (n : ℕ): f (a n) = f (a 0) + 2 * c * ∑ k in Finset.range n, x k := by
      induction' n with n ih
      · simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      · calc
          f (a (n + 1)) = f (a n) + 2 * c * (x n) := by exact hfsucc n
          _ = f (a 0) + 2 * c * ∑ k ∈ Finset.range n, x k + 2 * c * (x n) := by
            exact congrFun (congrArg HAdd.hAdd ih) (2 * c * x n)
          _ = f (a 0) + 2 * c * ∑ k ∈ Finset.range (n + 1), x k := by
            rw [Finset.sum_range_succ x n]
            ring

    -- We now show that $f(a_0) \geq 2 b_0 + 2 n (f(y) - 2 y) + 4y$
    have himpos (n : ℕ) : f (a 0) ≥ 2 * x 0 + 2 * n * (f y - 2 * y) + 4 * y := by

      -- We calculate that
      -- $$
      --  \begin{aligned} f(a_n) & = f(a_0) + 2 c \sum_{i=0}^{n-1} \left( \left(b_0 + \frac{f(y) - 2 y}{c}\right)(c+1)^i - \frac{f(y) - 2 y}{c} \right) \\
      --   & = f(a_0) + 2 \left(b_0 + \frac{f(y) - 2 y}{c}\right) \left((c+1)^n - 1\right) - 2 n (f(y) - 2 y). \end{aligned}
      -- $$
      -- Since $f(a_n) \geq 2 a_n = 2 b_n + 4 y$,
      -- $$
      --     \begin{aligned} & f(a_0) + 2 \left(b_0 + \frac{f(y) - 2 y}{c}\right) \left((c+1)^n - 1\right) - 2 n (f(y) - 2 y) \\
      --     & \geq 2 b_n + 4 y \\
      --     & =  2 \left(b_0 + \frac{f(y) - 2 y}{c}\right)(c+1)^n - 2 \frac{f(y) - 2 y}{c} + 4y \end{aligned}
      -- $$
      have := calc f (a 0) + 2 * (x 0 + (f y - 2 * y) / c) * ((c + 1) ^ n - 1) - 2 * n * (f y - 2 * y)
        _ = f (a 0) + 2 * c * ∑ k ∈ Finset.range n, ((x 0 + (f y - 2 * y) / c) * (c + 1) ^ k - (f y - 2 * y) / c) := by
          have := geom_sum_eq (show (c + 1 ≠ 1) by linarith) n
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, this]
          simp only [add_sub_cancel_right, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
          ring
        _ = f (a 0) + 2 * c * ∑ k ∈ Finset.range n, x k := by
          simp only [pow_zero, mul_one, add_sub_cancel_right, Finset.sum_sub_distrib,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul, x]
        _ = f (a n) := Eq.symm (hfsum n)
        _ ≥ 2 * a n := by
          apply hflb (a n)
          linarith [hapos n]
        _ = 2 * x n + 4 * y := by
          ring
        _ =  2 * (x 0 + (f y - 2 * y) / c) * (c + 1) ^ n - 2 * (f y - 2 * y) / c + 4 * y := by
          simp only [pow_zero, mul_one, add_sub_cancel_right, x]
          field_simp
          ring

      -- Then with basic manipulations we complete the claimed inequality
      rw [mul_sub_left_distrib, ge_iff_le, le_sub_iff_add_le, mul_one, ← tsub_le_iff_right] at this
      field_simp at this
      ring_nf at this
      rw [mul_inv_cancel₀ (show c ≠ 0 by linarith), mul_comm, add_comm, ← add_sub_assoc, one_mul] at this
      ring_nf at this
      field_simp at this
      field_simp [x, a]
      ring_nf
      field_simp
      nth_rw 3 [add_comm]
      nth_rw 2 [mul_comm]
      apply this

    -- This is false for sufficiently large $n$
    let n' := (f (a 0) - 2 * x 0 - 4 * y) / (f y - 2 * y) / 2
    let n := ⌈n'⌉₊ + 1
    specialize himpos n
    have hn : n' < n := by
      have := Nat.le_ceil n'
      push_cast
      linarith

    have : f (a 0) = n' * (f y - 2 * y) * 2 + 2 * x 0 + 4 * y := by
      simp only [pow_zero, mul_one, add_sub_cancel_right, n', x]
      field_simp
      ring

    rw [this, ge_iff_le, add_le_add_iff_right, add_comm, add_le_add_iff_right, mul_assoc,
      mul_comm] at himpos
    simp only [Nat.ofNat_pos, mul_le_mul_right, mul_le_mul_right hfy] at himpos
    refine (lt_self_iff_false ↑n).mp ?_
    exact lt_imp_lt_of_le_imp_le (fun a => himpos) hn

  -- Combining the above inequalities gives us $f(x) = 2 x$ for all $x > 0$.
  intro x hx
  exact le_antisymm (hfub x hx) (hflb x hx)

  -- It is simple to show that the answer does solve the problem
  intro h x y hxpos hypos
  rw [h y hypos, h (x + 2 * y) (by positivity), h ((c + 1) * x + 2 * y) (by positivity)]
  ring
