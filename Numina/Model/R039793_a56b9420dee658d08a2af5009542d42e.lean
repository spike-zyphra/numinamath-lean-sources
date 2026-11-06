import Mathlib

def S : ℕ → ℤ
| n => ∑ k in Finset.range (n + 1), k

theorem algebra_289028 (n : ℕ) : S n = n * (n + 1) / 2 := by
  rw [S]
  have h1 : ∀ (n : ℕ), (∑ k in Finset.range (n + 1), (k : ℤ)) = (n * (n + 1) / 2 : ℤ) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      cases n with
      | zero =>
        all_goals
          norm_num
      | succ n =>
        simp [add_assoc, mul_add] at *
        <;> ring_nf
        <;> omega
  specialize h1 n
  simpa using h1