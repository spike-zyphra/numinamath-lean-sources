import Mathlib

/- Let $E$ be a positive integer such that $E \ge 4$ and $E \equiv 1 \pmod 4$. Determine the last four digits of $5^E$. Show the answer is $3125$. -/
theorem number_theory_634973 (E : ℕ) (h₀ : 4 ≤ E) (h : E ≡ 1 [MOD 4]) :
    (5 ^ E) % 10000 = 3125 := by
  -- We show that E = 4k + 1 for some k.
  simp [Nat.ModEq] at h
  obtain ⟨k, rfl⟩ : ∃ k, E = 4 * k + 1 := by
    -- Let k := E / 4.
    use E / 4
    rw [← h, Nat.div_add_mod E 4]
  -- The condition that E ≥ 4 is equivalent to 1 ≤ k.
  replace h₀ : 1 ≤ k := by omega
  clear h
  -- We induct on k.
  induction k, h₀ using Nat.le_induction with
  | base => simp -- The base case is trivial.
  | succ k hk ih =>
    -- For the inductive step, we show that 5^{4k+5} % 10000 = 3125.
    -- 5^{4k+5} = 5^{4k+1} * 5^4 ≡ 3125 * 5^4 ≡ 3125 [MOD 10000].
    rw [Nat.mul_succ, add_assoc, add_comm 4, ← add_assoc, pow_add, Nat.mul_mod, ih]
    rfl