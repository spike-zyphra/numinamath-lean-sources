import Mathlib

open Finset

/- On fixe un entier naturel $n \geqslant 2$. Déterminer tous les nombres réels $x \geqslant-1$ tels que pour tous nombres réels $a_{1}, \ldots, a_{n} \geqslant 1$ on ait
$$
\frac{a_{1}+x}{2} \times \cdots \times \frac{a_{n}+x}{2} \leqslant \frac{a_{1} a_{2} \cdots a_{n}+x}{2} .
$$ -/
theorem inequalities_605482
    (n : ℕ) (hn : 2 ≤ n) :
    {x : ℝ | -1 ≤ x ∧ ∀ a : ℕ → ℝ, (∀ i, 1 ≤ a i) → (∏ i ∈ range n, ((a i + x) / 2) ≤ ((∏ i ∈ range n, a i) + x) / 2)} = Set.Icc (-1 : ℝ) 1 := by

  -- lemma, if all $f i$ is greater than or equal to one, then $\prod_i f i$ is greater than or equal to one.
  have l_prod_gt_one (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ i ∈ Finset.range n, f i := by
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.prod_range_succ]
      exact one_le_mul_of_one_le_of_one_le ih (hf n)

  ext x
  rw [Set.mem_setOf_eq, Set.mem_Icc]

  constructor

  -- sufficiency
  . intro ⟨hx, h⟩
    simp_rw [hx, true_and, ge_iff_le]

    -- We start by setting $a_i = 1$ for all $i$.
    -- This gives us the condition: $$ \left(\frac{1+x}{2}\right)^n \leq \frac{1+x}{2}. $$
    specialize h (fun _ => 1) (by simp only [le_refl, implies_true])

    -- Let $y = \frac{1+x}{2}$.
    let y := (1 + x) / 2

    -- By hypothesis, $y \geq 0$.
    have t1 : 0 ≤ y := by
      apply div_nonneg (by linarith only [hx]) zero_le_two

    -- Since $y^n \leq y$, we have $y^{n-1} \leq 1$ and thus $y \leq 1$, which implies $x \leq 1$.
    have t2 : y ≤ 1 := by
      -- $y^n \leq y$
      have : y ^ n ≤ y := by
        simp_rw [prod_const, card_range, one_pow] at h
        convert h
      -- $y^{n-1} \leq 1$
      replace : y ^ (n - 1) ≤ 1 := by
        rcases LE.le.eq_or_gt hx with hx | hx
        -- if $x = -1$
        . simp only [hx, add_neg_cancel, zero_div, y]
          rw [zero_pow (by omega)]
          norm_num
        -- else $x \ge -1$, and $y \ne 0$
        have t_y_ne_zero : y ≠ 0 := by
          by_contra!
          dsimp [y] at this
          rcases div_eq_zero_iff.mp this
          <;> linarith
        convert mul_le_mul_of_nonneg_right this (inv_nonneg_of_nonneg t1)
        . rw [pow_sub₀ y t_y_ne_zero (by linarith), pow_one]
        . exact (mul_inv_cancel₀ t_y_ne_zero).symm
      -- thus $y \leq 1$
      convert (pow_le_one_iff_of_nonneg t1 (by omega)).mp this

    -- t2 implies $x \leq 1$.
    dsimp [y] at t2
    linarith

  -- necessity
  . intro ⟨h_xge, h_xle⟩
    -- Conversely, we need to show that any $x \in [-1, 1]$ works.
    simp_rw [h_xge, true_and]
    intro A h_Agtone

    -- We proceed by induction on $n$.
    -- we should begin with 1, so we create a temporary variable m
    suffices : ∀ m, ∏ i ∈ range (m + 1), ((A i + x) / 2) ≤ ((∏ i ∈ range (m + 1), A i) + x) / 2
    . specialize this (n - 1)
      convert this
      <;> omega

    -- re rename m with n to align with the solution
    intro n
    induction n with
    -- For $n=1$, the inequality is obvious.
    | zero =>
      simp
    -- Suppose it is true at rank $n-1$.
    | succ n ih =>
      -- The left-hand side of the inequality is then less than or equal to $\frac{a+x}{2} \times \frac{b+x}{2}$, where $a = a_1 a_2 \cdots a_{n-1}$ and $b = a_n$.
      set a := ∏ i ∈ range (n + 1), A i with ha
      set b := A (n + 1) with hb

      -- It then suffices to show that: $$ \left(\frac{a+x}{2}\right)\left(\frac{b+x}{2}\right) \leq \left(\frac{ab+x}{2}\right). $$
      suffices : ((a + x) / 2) * ((b + x) / 2) ≤ (a * b + x) / 2
      . conv => lhs; rw [prod_range_succ, ← hb]
        conv => rhs; rw [prod_range_succ, ← ha,← hb]
        trans (a + x) / 2 * ((b + x) / 2)
        . gcongr
          -- here, we just need to profe that $0 \le (b + x) / 2$
          rw [hb]
          refine div_nonneg (by linarith [h_Agtone (n + 1)]) zero_le_two
        exact this

      -- to show that: $$ \left(\frac{a+x}{2}\right)\left(\frac{b+x}{2}\right) \leq \left(\frac{ab+x}{2}\right). $$
      -- By expanding, the inequality becomes: $$ (a+b-2)x + x^2 \leq ab. $$
      suffices : (a + b - 2) * x + x ^ 2 ≤ a * b
      . linarith

      -- $1 \le a$
      have h_a_ge : 1 ≤ a := by
        rw [ha]
        apply l_prod_gt_one
        exact fun i => h_Agtone i

      -- $1 \le b$
      have h_b_ge : 1 ≤ b := by
        apply h_Agtone

      -- Since $a+b-2 \geq 0$, and since $x \leq 1$ and $x^2 \leq 1$, the left-hand side of the inequality is bounded by $(a+b-2) + 1$,
      -- so it suffices to show that $(a+b-2) + 1 \leq ab$,
      -- or equivalently that $0 \leq ab - a - b + 1$.
      suffices : 0 ≤ a * b - b + 1
      . nlinarith
      -- Now, we have $ab - a - b + 1 = (a-1)(b-1)$. Since $a \geq 1$ and $b \geq 1$, the inequality $(a-1)(b-1) \geq 0$ is indeed satisfied.
      nlinarith
