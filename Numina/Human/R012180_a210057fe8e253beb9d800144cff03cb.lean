import Mathlib

/-
Find the largest number $n$ such that (2004!)! is divisible by $((n!)!)!$.
-/
theorem number_theory_189489 :
  IsGreatest { n : ℕ | ((n.factorial).factorial).factorial ∣ ((2004).factorial).factorial} 6 := by

  -- We first show that if $a$ and $b$ are positive natural numbers,
  -- then $a! \leq b!$ iff $a \leq b$.
  have h₁ {a b : ℕ} (ha : a > 0) (hb : b > 0)
    : a.factorial ≤ b.factorial ↔ a ≤ b := by
    constructor
    . intro h
      by_contra g
      simp at g
      apply Nat.factorial_lt_of_lt hb at g
      omega
    . apply Nat.factorial_le

  -- Then, we show that if $a$ and $b$ are positive natural numbers,
  -- then $a!$ divides $b!$ iff $a! \leq b!$.
  have h₂ {a b : ℕ} (ha : a > 0) (hb : b > 0)
    : a.factorial ∣ b.factorial ↔ a.factorial ≤ b.factorial := by
    constructor
    . apply Nat.le_of_dvd
      apply Nat.factorial_pos
    . intro h
      apply Nat.factorial_dvd_factorial
      rw [← h₁ ha hb]
      exact h

  simp [IsGreatest, upperBounds]
  constructor
  . -- We show that when $n = 6$, $((n!)!)!$ divides $(2004!)!$.
    rw [h₂ (by simp [Nat.factorial_pos]) (by simp [Nat.factorial_pos])]
    rw [h₁]
    . rw [h₁]; repeat decide
    . apply Nat.factorial_pos
    . apply Nat.factorial_pos

  . -- Suppose that $a$ is such that $((a!)!)!$ divides $(2004!)!$.
    intro a ah

    -- By the second claim, we obtain that $((a!)!)! \leq (2004!)!$.
    apply (h₂ (by simp [Nat.factorial_pos]) (by simp [Nat.factorial_pos])).mp at ah

    -- We consider two cases, depending on whether or not $a = 0$.
    by_cases g : a = 0
    . -- Clearly, if $a = 0$, then $a \leq 6$.
      rw [g]; simp

    . -- Assume that $a > 0$.

      -- Apply the first claim twice to $((a!)!)! \leq (2004!)!$ to obtain that
      -- $a! \leq 2004$.
      apply (h₁ (by simp [Nat.factorial_pos]) (by simp [Nat.factorial_pos])).mp at ah
      apply (h₁ (by simp [Nat.factorial_pos]) (by simp [Nat.factorial_pos])).mp at ah

      -- We proceed by contradiction by assuming that $a > 6$.
      by_contra con

      -- Then there exists a natural number $m$ such that $a = m + 7$.
      have : ∃ m, a = m + 7 := by
        simp at con
        exact Nat.exists_eq_add_of_le' con

      -- Since $a! \leq 2004$, we obtain that $(m + 7)! \leq 2004.$
      obtain ⟨ m, hm ⟩ := this
      rw [hm] at ah

      -- But, $7! \leq (m + 7)!$.
      have : (7).factorial ≤ (m + 7).factorial := by apply Nat.factorial_le; norm_num

      -- Thus, $7! \leq 2004$.
      obtain g := Nat.le_trans this ah

      -- A simple computation shows that the inequality is false.
      revert g
      decide