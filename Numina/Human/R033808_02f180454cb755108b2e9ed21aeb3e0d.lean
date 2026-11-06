import Mathlib.Tactic.Linarith

/-- An $m\times n\times p$ rectangular box has half the volume of an
$(m + 2)\times(n + 2)\times(p + 2)$ rectangular box, where $m, n,$ and $p$ are
integers, and $m\le n\le p.$  What is the largest possible value of $p$? -/
theorem algebra_708 :
    (∃ m n : ℕ, 2 * m * n * 130 = (m + 2) * (n + 2) * (130 + 2)) ∧
    (∀ p : ℕ, (∃ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ 2 * m * n * p = (m + 2) * (n + 2) * (p + 2))
    → p ≤ 130) := by
  constructor
  -- $p 130$ is a valid solution because the conditions are satisfied for
  -- $m = 3, n = 11, p = 130$.
  · use 3, 11

  -- Let's show that this is the largest possible value of $p$.
  · rintro p ⟨m, n, hm, hn, h⟩

    -- $m$ must be at least $3$ because $m = 0, 1, 2$ do not lead to a solution.
    have hm : 3 ≤ m := by
      by_contra! hm'
      match m with
      | Int.ofNat m =>
        match m with
        | 0 => simp at h; rcases h with h | h <;> linarith
        | 1 => simp at h; nlinarith
        | 2 => simp at h; linarith

    -- Likewise, $n$ must be at least $3$.
    have hn : 3 ≤ n := by
      by_contra! hn'
      match n with
      | Int.ofNat n =>
        match n with
        | 0 => simp at h; rcases h with h | h <;> linarith
        | 1 => simp at h; nlinarith
        | 2 => simp at h; linarith

    -- Set $a = m - 2$ and $b = n - 2$ in order to simplify calculations.
    set a := m - 2 with ha
    have : m = a + 2 := by linarith
    rw [this] at h

    set b := n - 2 with hb
    have : n = b + 2 := by linarith
    rw [this] at h

    -- Notice that $a + b \leq a*b + 1$ because $0 ≤ (a - 1)*(b - 1)$
    have : 0 ≤ (a - 1)*(b - 1) := by nlinarith
    have : a + b ≤ a*b + 1 := by linarith

    -- Interms of $a$ and $b$, the equation becomes, after simplification,
    -- $p(a*b - 8) = 2*a*b + 8*(a + b) + 32$.
    have : p * (a*b - 8) = 2 * (a + 4) * (b + 4) := by linarith
    have : 2 * (a + 4) * (b + 4) = 2*a*b + 8*(a + b) + 32 := by linarith

    -- Notice that $a*b - 8$ must be positive because the right hand side is positive.
    have hab : 0 < a*b - 8 := by nlinarith

    -- Now using $(a + b) ≤ (a*b + 1)$ and simplifying, we get the inequality
    -- $p(a*b - 8) ≤ 10*(a*b - 8) + 120$.
    have : 2*a*b + 8*(a + b) + 32 ≤ 2*a*b + 8*(a*b + 1) + 32 := by nlinarith
    have : 2*a*b + 8*(a*b + 1) + 32 = 10*(a*b - 8) + 120 := by linarith
    have : p * (a*b - 8) ≤ 10*(a*b - 8) + 120 := by linarith

    -- Then combining everyting, we get $p ≤ 130$.
    nlinarith