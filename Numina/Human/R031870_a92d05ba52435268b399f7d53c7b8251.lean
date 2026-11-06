import Mathlib
open Real
/- 2. Find all values of $y$, for each of which no value of $x$ satisfying the inequality $\log _{2}(|x|+|y|) \leqslant 2, \quad$ satisfies the inequality $\log _{\frac{1}{2}}(|x|+|y+4|) \geqslant-2$ -/
theorem inequalities_188095 (y : ℝ) : (¬(∃ x, logb 2 (|x| + |y|) ≤ 2 ∧ logb (1/2) (|x| + |y + 4|) ≥ -2)) ↔ (y < -4 ∨ y > 0):= by
  -- First lemma: For any non-negative real x, log_2(x) ≤ 2 is equivalent to x ≤ 2^2
  have g1 : ∀ x : ℝ, x ≥ 0 → (logb 2 x ≤ 2 ↔ x ≤ 2 ^ 2):= by
    intro x hx
    by_cases hx1 : x = 0
    .
      subst x
      simp
    .
      -- If x > 0, we can use properties of logarithms
      replace hx : x > 0 := by
        by_contra H
        simp at H
        replace H : x = 0:= by linarith
        trivial
      have h : logb 2 x ≤ 2 ↔ x ≤ 2 ^ (2 : ℝ):= Real.logb_le_iff_le_rpow (show 1 < 2 by norm_num) hx
      simp at h
      exact h

  -- Second lemma: For any non-negative real x, log_(1/2)(x) ≥ -2 is equivalent to x ≤ 2^2
  have g2 : ∀ x : ℝ, x ≥ 0 → (logb (1/2) x ≥ -2 ↔ x ≤ 2 ^ 2):= by
    intro x hx
    rw [←Real.log_div_log]
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
    constructor
    .
      -- Forward direction: log_(1/2)(x) ≥ -2 implies x ≤ 2^2
      intro h
      rw [show log x / -log 2 = -(log x / log 2) by ring] at h
      replace h : log x / log 2 ≤ 2:= by linarith
      rw [Real.log_div_log] at h
      exact (g1 x hx).1 h
    .
      -- Reverse direction: x ≤ 2^2 implies log_(1/2)(x) ≥ -2
      intro h
      replace g1:= (g1 x hx).2 h
      rw [show log x / -log 2 = -(log x / log 2) by ring]
      rw [Real.log_div_log]
      linarith

  -- Main proof: bidirectional implication
  constructor
  .
    -- Forward direction: If no x satisfies both inequalities, then y < -4 or y > 0
    intro h
    by_contra H
    simp at H
    rcases H with ⟨H1, H2⟩
    absurd h
    use 0
    constructor
    .
      -- Showing that x = 0 satisfies the first inequality when -4 ≤ y ≤ 0
      rw [show |0| + |y| = |y| by simp]
      rw [show |y| = -y by exact abs_of_nonpos (by linarith)]
      exact (g1 (-y) (by linarith)).2 (by linarith)
    .
      -- Showing that x = 0 satisfies the second inequality when -4 ≤ y ≤ 0
      rw [show |0| + |y + 4| = |y + 4| by simp]
      rw [show |y + 4| = y + 4 by exact abs_of_nonneg (by linarith)]
      exact (g2 (y + 4) (by linarith)).2 (by linarith)
  .
    -- Reverse direction: If y < -4 or y > 0, then no x satisfies both inequalities
    intro h
    by_contra H
    rcases H with ⟨x, H1, H2⟩
    replace H1:= (g1 (|x| + |y|) (by positivity)).1 H1
    replace H2:= (g2 (|x| + |y + 4|) (by positivity)).1 H2
    rcases h with h | h
    .
      -- Case y < -4: Derive a contradiction using the first inequality
      replace h : |y| > 4:= by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have h1 : |x| ≥ 0:= by positivity
      linarith
    .
      -- Case y > 0: Derive a contradiction using the second inequality
      rw [show |y + 4| = y + 4 by exact abs_of_nonneg (by linarith)] at H2
      have h1 : |x| ≥ 0:= by positivity
      linarith
