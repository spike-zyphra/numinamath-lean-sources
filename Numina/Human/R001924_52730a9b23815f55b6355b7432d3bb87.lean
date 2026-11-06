import Mathlib

abbrev y : ℕ → ℤ := fun n =>
  match n with
  | 0 => 5
  | 1 => 31
  | n + 2 => 6 * y (n + 1) - y n

/- Consider the sequence $\{a_n\}$ such that $a_0=4$, $a_1=22$, and $a_n-6a_{n-1}+a_{n-2}=0$ for $n\ge2$.  Prove that there exist sequences $\{x_n\}$ and $\{y_n\}$ of positive integers such that
\[
a_n=\frac{y_n^2+7}{x_n-y_n}
\]
for any $n\ge0$. -/
theorem algebra_45662 (a : ℕ → ℤ) (h0 : a 0 = 4) (h1 : a 1 = 22)
  (h : ∀ n ≥ 2, a n - 6 * a (n - 1) + a (n - 2) = 0) :
  ∃ x y : ℕ → ℤ, (∀ n, x n > 0) ∧ (∀ n, y n > 0) ∧ (∀ n, a n * (x n - y n) = (y n ^ 2 + 7)) := by
  -- Propose the candidate sequences for `x` and `y`.
  use (fun n => y n + 2 * a n), y
  -- Prove a crucial helper lemma containing two identities that hold for all `n`.
  have h₁ : ∀ n, 2 * a (n + 1) * a n - 21 = y (n + 1) * y n ∧
    2 * a n ^ 2 - 7 = y n ^ 2 := by
    -- The proof of the lemma is by strong induction on `n`.
    intro n
    induction n using Nat.strongRecOn
    rename_i n ih
    -- Base case: n = 0.
    by_cases hn : n = 0
    · simp [hn, h0, h1, y]
    · -- Base case: n = 1.
      by_cases hn1 : n = 1
      · -- The proof for n=1 requires calculating a 2 = 128.
        suffices a 2 = 128 by
          simp [hn1, h1, this, y]
        linarith [h 2 (by omega)]
      · -- Inductive step for n ≥ 2.
        have h' := h n (by omega)
        -- First, prove 2 * a n ^ 2 - 7 = y n ^ 2.
        have h'' : 2 * a n ^ 2 - 7 = y n ^ 2 := by
          -- Isolate a n from the recurrence relation.
          replace h' : a n = 6 * a (n - 1) - a (n - 2) := by linarith
          -- Substitute the recurrence relations for both a n and y n.
          rw [h', show y n = y (n - 2 + 2) by congr; omega, y, show n - 2 + 1 = n - 1 by omega]
          -- Apply the induction hypothesis for n-2 and n-1.
          have g1 := ih (n - 2) (by omega)
          have g2 := ih (n - 1) (by omega)
          -- Simplify the expression algebraically.
          ring_nf
          -- Use the identities from the induction hypotheses to rewrite the expression.
          rw [← g1.2, ← g2.2]
          ring_nf
          -- Use the first identity from the induction hypothesis for n-2.
          have := ih (n - 2) (by omega) |>.1
          rw [show n - 2 + 1 = n - 1 by omega] at this
          rw [← this]
          ring
        -- Now, prove 2 * a n * a (n + 1) - 21 = y n * y (n + 1) which needs 2 * a n ^ 2 - 7 = y n ^ 2.
        refine ⟨?_, h''⟩
        -- Get the recurrence relation for a(n+1).
        have g1 := h (n + 1) (by omega)
        rw [show n + 1 - 1 = n by omega, show n + 1 - 2 = n - 1 by omega] at g1
        -- Isolate a(n+1).
        replace g1 : a (n + 1) = 6 * a n - a (n - 1) := by linarith
        -- Substitute the recurrence relations for a(n+1) and y(n+1).
        rw [g1, show y (n + 1) = y (n - 1 + 2) by congr 1; omega, y, show n - 1 + 1 = n by omega]
        -- Simplify algebraically.
        ring_nf
        -- Apply the induction hypothesis for n-1.
        have g2 := ih (n - 1) (by omega)
        rw [show n - 1 + 1 = n by omega] at g2
        rw [← h'', ← g2.1]
        ring
  -- Prove that all terms of the sequence `a` are positive.
  have ha : ∀ n, a n > 0 := by
    -- This is proven by showing a stronger property: `a` is positive and strictly increasing.
    have P : ∀ n, a n > 0 ∧ a (n + 1) > a n := by
      intro n
      -- Use simple induction.
      induction n with
      | zero => simp [h0, h1]
      | succ k ih =>
        have ⟨hk_pos, hk_inc⟩ := ih
        refine ⟨by linarith, ?_⟩
        -- Get the recurrence relation for a(k+2) to prove the inequality.
        have h_rec : a (k + 2) = 6 * a (k + 1) - a k := by
          specialize h (k + 2) (by simp)
          rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega] at h
          linarith [h]
        rw [h_rec]
        linarith [hk_inc, hk_pos]
    intro n
    exact (P n).left
  -- Similarly, prove that all terms of the sequence `y` are positive.
  have hy : ∀ n, y n > 0 := by
    -- This is also proven by showing `y` is positive and strictly increasing.
    have P : ∀ n, y n > 0 ∧ y (n + 1) > y n := by
      intro n
      induction n with
      | zero => simp [y]
      | succ k ih =>
        have ⟨hk_pos, hk_inc⟩ := ih
        refine ⟨by linarith, ?_⟩
        have h_rec : y (k + 2) = 6 * y (k + 1) - y k := by
          simp [y]
        rw [h_rec]
        linarith [hk_inc, hk_pos]
    intro n
    exact (P n).left
  refine ⟨fun n => by linarith [ha n, hy n], fun n => hy n, fun n => ?_⟩
  -- Finally, prove the main equation `a n * (x n - y n) = y n ^ 2 + 7`.
  by_cases hn : n = 0
  · simp [hn, h0, y]
  · by_cases hn1 : n = 1
    · simp [hn1, h1, y]
    · -- For the general case n ≥ 2. We have 2 * a n ^ 2 - 7 = y n ^ 2.
      have hn2 : n ≥ 2 := by omega
      simp [y, ← h₁ n]
      ring