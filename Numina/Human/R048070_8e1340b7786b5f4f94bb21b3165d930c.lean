import Mathlib

/-2. A2 (ROM) An infinite sequence $a_{0}, a_{1}, a_{2}, \ldots$ of real numbers satisfies the condition  $$ a_{n}=\left|a_{n+1}-a_{n+2}\right| \text { for every } n \geq 0 $$  with $a_{0}$ and $a_{1}$ positive and distinct. Can this sequence be bounded?-/
theorem algebra_25173 {a : ℕ → ℝ} (pos_a0_a1 : 0 < a 0 ∧ 0 < a 1) (a0_ne_a1 : a 0 ≠ a 1)
(ha : ∀ n, a n = |a (n + 1) - a (n + 2)|) : ¬ BddAbove (a '' Set.univ) := by
-- For the general case, we first apply ne_iff_lt_or_gt at the assumption a0_ne_a1 and split the goal to two cases
  wlog h : a 0 < a 1
  · push_neg at h; replace h : a 1 < a 0 := by
      rw [lt_iff_le_and_ne]; exact ⟨h, by symm; exact a0_ne_a1⟩
    have a1_lt_a2 : a 1 < a 2 := by
      have := ha 0; simp at this; symm at this
      rw [abs_eq] at this; rcases this with h'|h'
      · apply_fun (fun t => a 1 - t) at h'; ring_nf at h'
        have : 0 ≤ a 2 := by rw [ha 2]; apply abs_nonneg
        linarith
      apply_fun (fun t => a 1 - t) at h'; ring_nf at h'
      any_goals linarith
  -- Define sequence $b$ to be the sequence of $a$ deleting the first term $a_0$ and apply the special case algebra_25173_1 to $b$
    let b : ℕ → ℝ := fun n => a (n + 1)
    have : ¬BddAbove (b '' Set.univ) := by
      apply this; any_goals simp [b]
      · constructor; any_goals linarith
      · linarith only [a1_lt_a2]
      · intro n; rw [ha (n+1)]
      exact a1_lt_a2
  -- Simplify this and finish the final goal
    rw [not_bddAbove_iff] at this; simp [b] at this
    rw [not_bddAbove_iff]; intro N; simp
    rcases this N with ⟨w, hw⟩; use w+1
-- Denote the minimum of $a_0$, $a_1$ and $a_1-a_0$ by $l$
  let l := a 0 ⊓ a 1 ⊓ (a 1 - a 0)
-- Prove $l$ is positive
  have lpos : 0 < l := by simp [l]; split_ands; any_goals linarith
-- Since $l$ is the minimum of the three, it has to be less or equal to any of them
  have hl : l ≤ a 0 ∧ l ≤ a 1 ∧ l ≤ a 1 - a 0 := by simp [l]
-- Use strong induction to prove that for any $n$, $a_n$ is always greater or equal to $l$
  have agel : ∀ n, l ≤ a n := by
    intro n; induction n using Nat.strong_induction_on with
    | h n hn =>
  -- Prove the case when $n$ is $0$, $1$ or $2$
    by_cases h : n ≤ 2; interval_cases n; any_goals linarith
    · have := ha 0; symm at this; norm_num at this
      rw [abs_eq] at this; rcases this with h'|h'
      any_goals linarith
  -- Assume $n$ is greater or equal to $3$, apply the assumption ha at $n-1$, $n-2$ and $n-3$
  -- then apply the induction hypothesis and use linarith to finish the goals
    push_neg at h; replace h : 3 ≤ n := by linarith
    have := ha (n-2)
    rw [show n-2+1=n-1 by omega] at this
    rw [show n-2+2=n by omega] at this
    by_cases h' : a (n - 1) ≤ a n
    · rw [abs_eq_neg_self.mpr] at this
      apply_fun (fun t => t + a (n-1)) at this; ring_nf at this
      have := hn (n-1) (show _ by omega)
      have := hn (n-2) (show _ by omega)
      any_goals linarith
    push_neg at h'; rw [abs_eq_self.mpr] at this
    apply_fun (fun t => t + a n - a (n - 2)) at this; ring_nf at this
    rw [add_comm, ← sub_eq_add_neg] at this
    replace this : a n = a (n - 3) := by
      have r := ha (n-3)
      rw [show n-3+2=n-1 by omega] at r
      rw [show n-3+1=n-2 by omega] at r
      rw [← abs_neg, neg_sub, ← this, abs_eq_self.mpr] at r; symm; assumption
      have := ha n; rw [this]; apply abs_nonneg
    rw [this]; apply hn; zify; rw [Nat.cast_sub]; simp; any_goals linarith
-- Define $b_n$ to be the sum of three consecutive terms $a_3n$, $a_3n+1$ and $a_3n+2$
  let b : ℕ → ℝ := fun n => a (3 * n) + a (3 * n + 1) + a (3 * n + 2)
-- Prove that $b_n$ is positive
  have bpos : ∀ n, 0 < b n := by
    intro n; simp [b]; repeat apply add_pos
    · suffices : l ≤ a (3 * n); linarith; apply agel
    · suffices : l ≤ a (3 * n + 1); linarith; apply agel
    suffices : l ≤ a (3 * n + 2); linarith; apply agel
-- Prove that it is enough to prove the final goal by showing that $b_n$ is not bounded above
  suffices b_unbounded : ¬ BddAbove (b '' Set.univ)
  · rw [not_bddAbove_iff]; intro N; simp
    rw [not_bddAbove_iff] at b_unbounded; simp [b] at b_unbounded
    rcases b_unbounded (3*N) with ⟨m, hm⟩
    by_cases h : a (3 * m) ≤ N ∧ a (3 * m + 1) ≤ N ∧ a (3 * m + 2) ≤ N
    · linarith
    repeat rw [Classical.not_and_iff_or_not_not] at h
    repeat rw [not_le] at h
    rcases h with h|h|h; use 3*m; use 3*m+1; use 3*m+2
  rw [not_bddAbove_iff]; intro N; simp
-- Prove that it is enough to prove $b_n$ is not bounded above by showing $b_n+1$ minus $b_n$ is always greater or equal to $l$
  suffices stepb : ∀ n, l ≤ b (n + 1) - b n
  · have : ∀ n, n * l + b 0 ≤ b n := by
      intro n; induction n with
      | zero => simp
      | succ n ih => push_cast; have := stepb n; linarith
    use Int.natAbs ⌊N / l⌋ + 1
    have r := this (Int.natAbs ⌊N / l⌋ + 1)
    have s : N < ↑(⌊N / l⌋.natAbs + 1) * l := by
      rw [← div_lt_iff₀]; push_cast
      suffices t : N / l < ↑⌊N / l⌋ + 1
      · have u := @Int.le_natAbs ⌊N / l⌋
        rify at u; rw [show |(⌊N / l⌋:ℝ)|=⌊N / l⌋.natAbs by rw [Int.cast_natAbs]; simp] at u
        linarith
      apply Int.lt_floor_add_one; assumption
    have : ↑(⌊N / l⌋.natAbs + 1) * l < ↑(⌊N / l⌋.natAbs + 1) * l + b 0 := by
      have := bpos 0; apply lt_add_of_pos_right; assumption
    linarith
-- To prove that two consecutive terms of $b_n$ always have a difference greater than $l$, we explicitly compute
-- $b_n+1-b_n$ in every possible case in terms of the first two terms $a_3n$ and $a_3n+1$
  intro n; simp [b]; ring_nf
  have := agel (1+n*3); have := agel (n*3)
-- Prove that $a_3n$ is not equal to $a_3n+1$ and split to two symmetric cases : $a_3n$ is less than $a_3n+1$ or $a_3n+1$ is less than $a_3n$
  have : a (3 * n) ≠ a (3 * n + 1) := by
    intro h'; suffices : 1 ≤ n
    · have := ha (3*n-1)
      rw [show 3*n-1+1=3*n by omega] at this
      rw [show 3*n-1+2=3*n+1 by omega] at this
      rw [h'] at this; norm_num at this
      have := agel (3*n-1); linarith
    by_contra h''; simp at h''; simp [h''] at h'; linarith
  ring_nf at this; rw [ne_iff_lt_or_gt] at this; rcases this with h|h
-- In the first case, prove $a_3n+1$ minus $a_3n$ is greater or equal to $l$
  · replace h : l ≤ a (1 + n * 3) - a (n * 3) := by
      by_cases h' : n < 1
      · simp at h'; simp [h']; linarith
      push_neg at h'; have := ha (3*n-1)
      rw [show 3*n-1+1=3*n by omega] at this
      rw [show 3*n-1+2=3*n+1 by omega] at this
      rw [abs_eq_neg_self.mpr] at this; ring_nf at this
      rw [add_comm, ← sub_eq_add_neg] at this
      rw [← this]; apply agel; ring_nf; linarith
  -- Apply ha at $3n$ and simplify the absolute value by using abs_eq
    have := ha (3*n); symm at this; rw [abs_eq] at this
    cases this; rename_i h1
    · apply_fun (fun t => a (3 * n + 1) - t) at h1; ring_nf at h1
    -- Apply ha at $3n+1$ and simplify the absolute value by using abs_eq
      have := ha (1+n*3); symm at this; rw [abs_eq] at this
      cases this; rename_i h2
      · apply_fun (fun t => a (3 * n + 2) - t) at h2; ring_nf at h2
        rw [h1] at h2; norm_num at h2
      -- In this special case, we derive a negative relation h2 between two terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
        have := agel (3+n*3); have := agel (n*3); linarith
      rename_i h2; apply_fun (fun t => a (3 * n + 2) - t) at h2; ring_nf at h2
      rw [h1] at h2; ring_nf at h2
    -- Apply ha at $3n+2$ and simplify the absolute value by using abs_eq
      have := ha (2+n*3); symm at this; rw [abs_eq] at this; ring_nf at this
      cases this; rename_i h3
      · apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
        rw [h1, h2] at h3; ring_nf at h3
      -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
        have := ha (3+n*3); symm at this; rw [abs_eq] at this; ring_nf at this
        cases this; rename_i h4
        · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
          rw [h3, h2] at h4; ring_nf at h4
        -- In this special case, we derived a negative relation h4 among terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
          have := agel (5+n*3); linarith
        rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
        rw [h3, h2] at h4; ring_nf at h4; rw [h1, h2, h3, h4]; ring_nf
        any_goals linarith
      rename_i h3; apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
      rw [h1, h2] at h3; ring_nf at h3
    -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
      have := ha (3+n*3); symm at this; rw [abs_eq] at this; ring_nf at this
      cases this; rename_i h4
      · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
        rw [h3, h2] at h4; ring_nf at h4
      -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
        rw [h1, h2, h3, h4]; ring_nf; linarith
      rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      rw [h3, h2] at h4; ring_nf at h4
      rw [h1, h2, h3, h4]; ring_nf; any_goals linarith
    rename_i h1; apply_fun (fun t => a (3 * n + 1) - t) at h1; ring_nf at h1
  -- Apply ha at $3n+1$ and simplify the absolute value by using abs_eq
    have := ha (1+n*3); symm at this; rw [abs_eq] at this
    ring_nf at this; cases this; rename_i h2
    · apply_fun (fun t => a (3 * n + 2) - t) at h2; ring_nf at h2
      rw [h1] at h2; ring_nf at h2
    -- Apply ha at $3n+2$ and simplify the absolute value by using abs_eq
      have := ha (2+n*3); symm at this; rw [abs_eq] at this
      ring_nf at this; cases this; rename_i h3
      · apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
        rw [h1, h2] at h3; ring_nf at h3
      -- In this special case, we derived a negative relation h4 among terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
        have := agel (4+n*3); linarith
      rename_i h3; apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
      rw [h1, h2] at h3; ring_nf at h3
    -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
      have := ha (3+n*3); symm at this; rw [abs_eq] at this
      ring_nf at this; cases this; rename_i h4
      · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
        rw [h3, h2] at h4; ring_nf at h4
      -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
        rw [h1, h2, h3, h4]; ring_nf; linarith
      rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      rw [h3, h2] at h4; ring_nf at h4
      rw [h1, h2, h3, h4]; ring_nf; any_goals linarith
    rename_i h2; apply_fun (fun t => a (3 * n + 2) - t) at h2; ring_nf at h2
    rw [h1] at h2; ring_nf at h2
  -- Apply ha at $3n+2$ and simplify the absolute value by using abs_eq
    have := ha (2+n*3); symm at this; rw [abs_eq] at this
    ring_nf at this; cases this; rename_i h3
    · apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
      rw [h1, h2] at h3; ring_nf at h3
    -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
      have := ha (3+n*3); symm at this; rw [abs_eq] at this
      ring_nf at this; cases this; rename_i h4
      · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
        rw [h3, h2] at h4; ring_nf at h4
      -- In this special case, we derived a negative relation h4 among terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
        have := agel (5+n*3); linarith
      rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      rw [h3, h2] at h4; ring_nf at h4
      -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
      rw [h1, h2, h3, h4]; ring_nf; any_goals linarith
    rename_i h3; apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
    rw [h1, h2] at h3; ring_nf at h3
  -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
    have := ha (3+n*3); symm at this; rw [abs_eq] at this
    ring_nf at this; cases this; rename_i h4
    · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      rw [h3, h2] at h4; ring_nf at h4
    -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
      rw [h1, h2, h3, h4]; ring_nf; linarith
    rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
    rw [h3, h2] at h4; ring_nf at h4
    rw [h1, h2, h3, h4]; any_goals ring_nf; linarith
-- For the case $a_3n$ larger than $a_3n+1$, we first prove their difference is greater or equal to $l$
  replace h : l ≤ a (n * 3) - a (1 + n * 3) := by
    suffices : 1 ≤ n
    · have := ha (3*n-1)
      rw [show 3*n-1+1=3*n by omega] at this
      rw [show 3*n-1+2=3*n+1 by omega] at this
      rw [abs_eq_self.mpr] at this; ring_nf at this
      rw [← this]; apply agel; ring_nf ; linarith
    by_contra h'; simp at h'; simp [h'] at h; linarith
  -- Apply ha at $3n$ and simplify the absolute value by using abs_eq
  have := ha (n*3); symm at this; rw [abs_eq] at this
  cases this; rename_i h1
  · apply_fun (fun t => a (3 * n + 1) - t) at h1; ring_nf at h1
  -- In this special case, we derived a negative relation h4 among terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
    have := agel (2+n*3); linarith
  rename_i h1; apply_fun (fun t => a (3 * n + 1) - t) at h1; ring_nf at h1
-- Apply ha at $3n+1$ and simplify the absolute value by using abs_eq
  have := ha (1+n*3); symm at this; rw [abs_eq] at this
  ring_nf at this; cases this; rename_i h2
  · apply_fun (fun t => a (3 * n + 2) - t) at h2; ring_nf at h2
    rw [h1] at h2; ring_nf at h2
  -- Apply ha at $3n+2$ and simplify the absolute value by using abs_eq
    have := ha (2+n*3); symm at this; rw [abs_eq] at this
    ring_nf at this; cases this; rename_i h3
    · apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
      rw [h1, h2] at h3; ring_nf at h3
  -- In this special case, we derived a negative relation h4 among terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
      have := agel (4+n*3); linarith
    rename_i h3; apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
    rw [h1, h2] at h3; ring_nf at h3
  -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
    have := ha (3+n*3); symm at this; rw [abs_eq] at this
    ring_nf at this; cases this; rename_i h4
    · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      rw [h3, h2] at h4; ring_nf at h4
    -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
      rw [h1, h2, h3, h4]; ring_nf; linarith
    rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
    rw [h3, h2] at h4; ring_nf at h4
    rw [h1, h2, h3, h4]; ring_nf; any_goals linarith
  rename_i h2; apply_fun (fun t => a (3 * n + 2) - t) at h2; ring_nf at h2
  rw [h1] at h2; ring_nf at h2
-- Apply ha at $3n+2$ and simplify the absolute value by using abs_eq
  have := ha (2+n*3); symm at this; rw [abs_eq] at this
  ring_nf at this; cases this; rename_i h3
  · apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
    rw [h1, h2] at h3; ring_nf at h3
  -- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
    have := ha (3+n*3); symm at this; rw [abs_eq] at this
    ring_nf at this; cases this; rename_i h4
    · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
      rw [h3, h2] at h4; ring_nf at h4
    -- In this special case, we derived a negative relation h4 among terms of $a$, which can't happen since we have proved that all $a_n$ is greater or equal to $l$
      have := agel (5+n*3); linarith
    rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
    rw [h3, h2] at h4; ring_nf at h4
  -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
    rw [h1, h2, h3, h4]; ring_nf; any_goals linarith
  rename_i h3; apply_fun (fun t => a (3 * n + 3) - t) at h3; ring_nf at h3
  rw [h1, h2] at h3; ring_nf at h3
-- Apply ha at $3n+3$ and simplify the absolute value by using abs_eq
  have := ha (3+n*3); symm at this; rw [abs_eq] at this
  ring_nf at this; cases this; rename_i h4
  · apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
    rw [h3, h2] at h4; ring_nf at h4
  -- After writing our every terms in terms of $a_3n$ and $a_3n+1$, we plug in h1, h2, h3 and h4 to the goal and use linarith to finish
    rw [h1, h2, h3, h4]; ring_nf; linarith
  rename_i h4; apply_fun (fun t => a (3 * n + 4) - t) at h4; ring_nf at h4
  rw [h3, h2] at h4; ring_nf at h4
  rw [h1, h2, h3, h4]; ring_nf; all_goals linarith