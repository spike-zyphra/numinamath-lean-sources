import Mathlib
/- 45. Given the proposition $p$ : the equation $a^{2} x^{2}+a x-2=0$ has a solution in $[-1$, 1]; proposition $q$ : there is only one real number $x$ that satisfies the inequality $x^{2} + 2 a x + 2 a \leqslant 0$, if the proposition " $p$ or $q$ " is false, find the range of values for $a$. -/
theorem algebra_603787 : {a : ℝ | ¬((∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧ a ^ 2 * x ^ 2 + a * x - 2 = 0) ∨ ExistsUnique fun x : ℝ => x ^ 2 + 2 * a * x + 2 * a ≤ 0)} = Set.Ioo (-1) 0 ∪ Set.Ioo 0 1:= by
  ext a
  constructor
  -- Forward direction: if ¬(p ∨ q), then a ∈ (-1,0) ∪ (0,1)
  .
    intro h
    simp at h
    -- Proof by contradiction
    by_contra H
    -- Case analysis: a must be 0, ≤ -1, or ≥ 1
    replace H : a = 0 ∨ a ≤ -1 ∨ a ≥ 1:= by
      simp at H
      rcases H with ⟨H1, H2⟩
      by_cases h1 : a ≤ -1
      .
        right
        left
        exact h1
      .
        simp at h1
        replace H1:= H1 h1
        by_cases h2 : a = 0
        .
          left
          exact h2
        .
          replace H1 : a > 0:= by
            by_contra H2
            simp at H2
            replace H1 : a = 0:= by linarith
            trivial
          replace H2:= H2 H1
          right
          right
          exact H2
    rcases H with H | H | H
    -- Case 1: a = 0
    .
      subst a
      simp at h
      -- Show that q is true when a = 0, contradicting h
      absurd h
      use 0
      constructor
      .
        simp
      .
        intro y
        simp
        intro hy
        have h1 : y ^ 2 ≥ 0:= by positivity
        replace hy : y ^ 2 = 0:= by linarith
        simp at hy
        exact hy
    -- Case 2: a ≤ -1
    .
      rcases h with ⟨h1, h2⟩
      -- Show that p is true when a ≤ -1, contradicting h1
      absurd h1
      simp
      use (1 / a)
      set b:= -a with hb
      clear_value b
      replace hb : a = -b:= by linarith
      subst a
      simp at H ⊢
      refine ⟨?_, ?_, ?_⟩
      -- Show 1/a ≥ -1
      .
        field_simp
        have g1 : -b < 0:= by linarith
        suffices -1 * (-b) ≥ 1 / (-b) * (-b) by exact (mul_le_mul_right_of_neg g1).mp this
        rw [show 1 / (-b) * (-b) = 1 by field_simp]
        simp
        exact H
      -- Show 1/a ≤ 1
      .
        field_simp
        replace H : -b ≤ 0:= by linarith
        replace H : 1 / (-b) ≤ 0:= by exact one_div_nonpos.mpr H
        linarith
      -- Show the equation is satisfied
      .
        field_simp
        linarith
    -- Case 3: a ≥ 1
    .
      rcases h with ⟨h1, _⟩
      -- Show that p is true when a ≥ 1, contradicting h1
      absurd h1
      simp
      use (1 / a)
      refine ⟨?_, ?_, ?_⟩
      -- Show 1/a ≥ -1
      .
        replace H : 1 / a ≥ 0:= by positivity
        linarith
      -- Show 1/a ≤ 1
      .
        have g1 : a > 0:= by linarith
        suffices 1 / a * a ≤ a by exact (div_le_one₀ g1).mpr H
        rw [show 1 / a * a = 1 by field_simp]
        linarith
      -- Show the equation is satisfied
      .
        field_simp
        linarith
  -- Backward direction: if a ∈ (-1,0) ∪ (0,1), then ¬(p ∨ q)
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case 1: a ∈ (-1,0)
    .
      rcases h with ⟨h1, h2⟩
      simp
      constructor
      -- Show p is false: no solution in [-1,1]
      .
        intro x hx1 hx2
        by_contra H
        -- Factor the quadratic equation
        rw [show a ^ 2 * x ^ 2 + a * x - 2 = (a * x - 1) * (a * x + 2) by ring] at H
        simp at H
        have g1 : a ≠ 0:= by linarith
        rcases H with H | H
        -- If ax - 1 = 0, then x = 1/a
        .
          replace H : x = 1 / a:= by
            field_simp
            linarith
          subst x
          -- Show 1/a < -1, contradicting x ∈ [-1,1]
          have h3 : 1 / a < -1:= by
            suffices 1 / a * a > (-1) * a by exact one_div_lt_neg_one h2 h1
            rw [show 1 / a * a = 1 by field_simp]
            simp
            linarith
          linarith
        -- If ax + 2 = 0, then x = -2/a
        .
          replace H : x = -2 / a:= by
            field_simp
            linarith
          subst x
          -- Show -2/a > 2, contradicting x ∈ [-1,1]
          have h3 : -2 / a > 2:= by
            suffices -2 / a * a < 2 * a by exact (mul_lt_mul_right_of_neg h2).mp this
            rw [show -2 / a * a = -2 by field_simp]
            linarith
          linarith
      -- Show q is false: not exactly one solution
      .
        by_contra H
        rcases H with ⟨x, hx1, hx2⟩
        -- Rewrite the inequality as (x + a)² ≤ a(a - 2)
        replace hx1 : (x + a) ^ 2 ≤ a * (a - 2):= by linarith
        -- Show a(a - 2) > 0, so there are two solutions
        have g1 : a * (a - 2) > 0:= by
          replace h1 : a - 2 < 0:= by linarith
          exact mul_pos_of_neg_of_neg h2 h1
        set e:= a * (a - 2) with he
        clear_value e
        -- Show both -a + √e and -a - √e are solutions
        have g2:= hx2 (-a + √e) ?_
        have g3:= hx2 (-a - √e) ?_
        -- They are distinct, contradicting uniqueness
        .
          replace g1 : √e > 0:= by positivity
          linarith
        -- Verify -a - √e is a solution
        .
          simp
          suffices (-a - √e) ^ 2 + 2 * a * (-a - √e) + 2 * a = 0 by linarith
          ring_nf
          field_simp
          linarith
        -- Verify -a + √e is a solution
        .
          simp
          suffices (-a + √e) ^ 2 + 2 * a * (-a + √e) + 2 * a = 0 by linarith
          ring_nf
          field_simp
          linarith
    -- Case 2: a ∈ (0,1)
    .
      rcases h with ⟨h1, h2⟩
      simp
      constructor
      -- Show p is false: no solution in [-1,1]
      .
        intro x hx1 hx2
        by_contra H
        -- Factor the quadratic equation
        rw [show a ^ 2 * x ^ 2 + a * x - 2 = (a * x - 1) * (a * x + 2) by ring] at H
        simp at H
        have g1 : a ≠ 0:= by linarith
        rcases H with H | H
        -- If ax - 1 = 0, then x = 1/a
        .
          replace H : x = 1 / a:= by
            field_simp
            linarith
          subst x
          -- Show 1/a > 1, contradicting x ∈ [-1,1]
          have h3 : 1 / a > 1:= by exact one_lt_one_div h1 h2
          linarith
        -- If ax + 2 = 0, then x = -2/a
        .
          replace H : x = -2 / a:= by
            field_simp
            linarith
          subst x
          -- Show -2/a < -2, contradicting x ∈ [-1,1]
          have h3 : -2 / a < -2:= by
            suffices -2 / a * a < (-2) * a by exact (mul_lt_mul_iff_of_pos_right h1).mp this
            rw [show -2 / a * a = -2 by field_simp]
            linarith
          linarith
      -- Show q is false: no solution exists
      .
        by_contra H
        rcases H with ⟨x, hx1, _⟩
        -- Rewrite the inequality as (x + a)² ≤ a(a - 2)
        replace hx1 : (x + a) ^ 2 ≤ a * (a - 2):= by linarith
        -- Show a(a - 2) < 0, contradicting (x + a)² ≥ 0
        have g1 : a * (a - 2) < 0:= by
          replace h2 : a - 2 < 0:= by linarith
          exact mul_neg_of_pos_of_neg h1 h2
        have g2 : (x + a) ^ 2 ≥ 0:= by positivity
        linarith
