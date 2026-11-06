import Mathlib

theorem algebra_204972 {a : ℕ → ℝ} (ha : ∀ i, a (i - 1) + a (i + 1) = 2 * a i)
    (ha' : a 0 ≠ a 1) :
    ∀ n, ∃ p : ℝ → ℝ, (∀ x, p x = ∑ i ∈ Finset.range (n + 1), a i * Nat.choose n i * (x ^ i * (1 - x) ^ (n - i))) ∧
    ∃ c d, ∀ x, p x = c * x + d := by
  intro n
  -- From the recurrence relation for i=0
  -- a(0-1) + a(0+1) = 2 * a 0
  have h1 := ha 0
  -- Since i=0, 0-1 is 0 in ℕ
  -- Also 0+1 = 1 in ℕ
  have h10 : a (0 - 1) = a 0 := by simp [Nat.zero_sub]
  have h11 : a (0 + 1) = a 1 := by simp
  -- Substitute these into the recurrence relation:
  rw [h10, h11] at h1
  -- We get a 0 + a 1 = 2 * a 0, which means a 1 = a 0
  have h2 : a 1 = a 0 := by linarith
  -- This contradicts the hypothesis that a 0 ≠ a 1
  exfalso
  exact ha' (Eq.symm h2)