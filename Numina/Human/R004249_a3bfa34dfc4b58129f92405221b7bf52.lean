import Mathlib

/- 1. Let $m$ and $n$ be positive numbers. Prove that
$$
\begin{aligned}
& x_{1}=x_{3}=x_{5}=\ldots=x_{99}=m \\
& x_{2}=x_{4}=x_{6}=\ldots=x_{100}=n
\end{aligned}
$$
is the unique solution to the system of equations
$$
\begin{aligned}
& n x_{1}=x_{2} x_{3}=x_{4} x_{5}=\ldots=x_{98} x_{99}=m x_{100} \\
& x_{1}+x_{2}=x_{3}+x_{4}=x_{5}+x_{6}=\ldots=x_{99}+x_{100}=m+n
\end{aligned}
$$
where all numbers $x_{1}, x_{2}, \ldots, x_{100}$ are positive. -/
theorem algebra_244793 (m n : ℝ) (x : ℕ → ℝ) (hm : 0 < m) (hn : 0 < n) :
    (∀ i ≤ 99, 0 < x i) ∧
    (∀ i ≤ 48, x (2 * i + 1) * x (2 * i + 2) = n * x 0) ∧
    (m * x 99 = n * x 0) ∧
    (∀ i ≤ 49, x (2 * i) + x (2 * i + 1) = m + n) ↔
    ∀ i ≤ 99, x i = if Even i then m else n := by
  symm
  constructor
  · intro h
    -- Show that x(i) = m for even i and x(i) = n for odd i works.
    -- We have x(0) = m and x(99) = n.
    have h0 : x 0 = m := by simp [h 0 (by norm_num)]
    have h99 : x 99 = n := by
      simp [h 99 (by norm_num), show ¬ Even 99 by decide]
    constructorm* _ ∧ _
    · -- x(i) > 0 for all i ≤ 99 because m > 0 and n > 0.
      intro i hi
      simp [h i hi]
      split_ifs <;> simp [hm, hn]
    · -- Show that x (2 * i + 1) * x (2 * i + 2) = n * x 0 = n * m.
      intro i hi
      rw [h (2 * i + 1) (by omega), h (2 * i + 2) (by omega), h0]
      rw [show 2 * i + 2 = (2 * i + 1) + 1 by linarith]
      -- If 2 * i + 1 is even then 2 * i + 2 is odd, and vice versa.
      -- So x(2 * i + 1) * x(2 * i + 2) = n * m.
      simp only [Nat.even_add_one, not_not]
      split_ifs <;> ring
    · -- m * x(99) = m * n = n * x(0).
      rw [h0, h99, mul_comm]
    · -- Show that x(2 * i) + x(2 * i + 1) = m + n.
      intro i hi
      rw [h (2 * i) (by linarith), h (2 * i + 1) (by linarith)]
      -- If 2 * i is even then 2 * i + 1 is odd, and vice versa.
      -- So x(2 * i) * x(2 * i + 1) = m + n.
      simp only [Nat.even_add_one]
      split_ifs <;> ring
  intro ⟨h_pos, h_mul, h99, h_add⟩
  -- Assume that x(i) > 0, x(2 * i + 1) * x(2 * i + 2) = n * x 0,
  -- m * x 99 = n * x0, x (2 * i) + x (2 * i + 1) = m + n.
  -- Show that x(i) = m if i is even and x(i) = n if i is odd.
  -- First, prove that x(0) = m.
  have h0 : x 0 = m := by
    -- Consider 3 cases: x(0) < m, x(0) = m, or x(0) > m.
    rcases lt_trichotomy (x 0) m with h0 | h0 | h0
    · -- If x(0) < m then m * x(99) = n * x(0) implies that x(99) < n.
      have h1 : x 99 < n := by nlinarith
      -- It is enough to show that x(2 * i) < m and n < x(2 * i + 1).
      suffices ∀ i ≤ 49, x (2 * i) < m ∧ n < x (2 * i + 1) by
        -- If n < x (2 * i + 1) then n < x(99), a contradiction.
        contrapose! h1
        linarith [this 49 (le_refl _)]
      intro i hi
      -- Proof by induction.
      induction i with
      | zero =>
        -- If i = 0 then x(0) < m and
        -- x(0) + x(1) = m + n implies x(1) > n.
        have h := h_add 0 (by norm_num)
        simp [h0] at h ⊢
        linarith
      | succ i ih =>
        -- Consider i + 1. We have x(2 * i) < m and n < x(2 * i + 1).
        -- We need to show that x(2 * i + 2) < m and n < x(2 * i + 3).
        replace ih := ih (by omega)
        -- Show that x(2 * i + 2) < m.
        have h : x (2 * (i + 1)) < m := by
          -- We have x(2 * i + 1) * x(2 * i + 2) = n * x(0).
          have h1 := h_mul i (by omega)
          rw [show 2 * (i + 1) = 2 * i + 2 by ring]
          -- Assume that m ≤ x(2 * i + 2) and show that
          -- x(2 * i + 1) * x(2 * i + 2) > n * x(0).
          contrapose! h1
          apply ne_of_gt
          calc
            -- We have n * x(0) ≤ n * m < x(2 * i + 1) * x(2 * i + 2).
            _ ≤ n * m := by gcongr
            _ < x (2 * i + 1) * x (2 * i + 2) := by
              apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ih.2 h1 (le_of_lt hn)
              apply h_pos
              omega
        -- x(2 * i + 2) + x(2 * i + 3) = m + n and x(2 *i + 2) < m,
        -- so n < x(2 * i + 3).
        have h1 := h_add (i + 1) hi
        simp [h]
        linarith
    · exact h0
    · -- If m < x(0) then m * x(99) = n * x(0) implies that n < x(99).
      have h1 : n < x 99 := by nlinarith
      -- It is enough to show that m < x(2 * i) and x(2 * i + 1) < n.
      suffices ∀ i ≤ 49, m < x (2 * i) ∧ x (2 * i + 1) < n by
        -- If x (2 * i + 1) < n then x(99) < n, a contradiction.
        contrapose! h1
        linarith [this 49 (le_refl _)]
      intro i hi
      -- Proof by induction.
      induction i with
      | zero =>
        -- If i = 0 then m < x(0) and
        -- x(0) + x(1) = m + n implies x(1) < n.
        have h := h_add 0 (by norm_num)
        simp [h0] at h ⊢
        linarith
      | succ i ih =>
        -- Consider i + 1. We have m < x(2 * i) and x(2 * i + 1) < n.
        -- We need to show that m < x(2 * i + 2) and x(2 * i + 3) < n.
        replace ih := ih (by omega)
        -- Show that m < x(2 * i + 2).
        have h : m < x (2 * (i + 1)) := by
          -- We have x(2 * i + 1) * x(2 * i + 2) = n * x(0).
          have h1 := h_mul i (by omega)
          rw [show 2 * (i + 1) = 2 * i + 2 by ring]
          -- Assume that x(2 * i + 2) ≤ m and show that
          -- x(2 * i + 1) * x(2 * i + 2) < n * x(0).
          contrapose! h1
          apply ne_of_lt
          calc
            _ ≤ n * m := by
              gcongr
              · linarith [h_pos (2 * i + 2) (by omega)]
              · exact le_of_lt ih.2
            _ < n * x 0 := by gcongr
        -- x(2 * i + 2) + x(2 * i + 3) = m + n and m < x(2 *i + 2),
        -- so x(2 * i + 3) < n.
        have h1 := h_add (i + 1) hi
        simp [h]
        linarith
  -- It is enough to show that x(2 * i) = m and x(2 * i + 1) = n for i ≤ 49.
  suffices ∀ i ≤ 49, x (2 * i) = m ∧ x (2 * i + 1) = n by
    intro i hi
    split_ifs with hi2
    · apply Nat.two_mul_div_two_of_even at hi2
      have := this (i / 2) (by omega)
      rw [hi2] at this
      exact this.1
    · simp at hi2
      have := this (i / 2) (by omega)
      rw [Nat.two_mul_div_two_add_one_of_odd hi2] at this
      exact this.2
  intro i hi
  -- Proof by induction.
  induction i with
  | zero =>
    -- If i = 0 then x(0) = m and x(0) + x(1) = m + n imply that x(1) = n.
    have h := h_add 0 (by norm_num)
    simp [h0] at h ⊢
    exact h
  | succ i ih =>
    -- Consider i + 1. We have x(2 * i) = m and x(2 * i + 1) = n.
    -- We need to show that x(2 * i + 2) = m and x(2 * i + 3) = n.
    have ⟨h_even, h_odd⟩ := ih (by linarith)
    -- Show that x(2 * i + 2) = m.
    have eq1 : x (2 * (i + 1)) = m := by
      -- We have x(2 * i + 1) * x(2 * i + 2) = n * x(0) = n * m.
      have h := h_mul i (by linarith)
      rw [show 2 * (i + 1) = 2 * i + 2 by ring]
      -- So x(2 * i + 2) = m (because x(2 * i + 1) = n).
      nlinarith
    -- We have x(2 * i + 2) = m and x(2 * i + 2) + x(2 * i + 3) = m + n,
    -- so x(2 * i + 3) = n.
    have h := h_add (i + 1) (by linarith)
    simp [eq1]
    linarith