import Mathlib

/- Definition of mutually relative prime, same as in Problem 4517 and 4518. -/
def MutuallyRelativePrime2 (s : Finset ℕ) := s.gcd id = 1

/- The solution set. -/
def s : Finset ℕ := {6, 10, 15, 30}

/- Find four integers that are mutually relatively prime, such that any two of these integers are not relatively prime. -/
theorem number_theory_4520 :
    s.card = 4 ∧ MutuallyRelativePrime2 s ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬Nat.Coprime x y := by
  refine ⟨?_, ?_, fun x hx y hy ne => ?_⟩
  -- Check S.card=4 .
  · simp [s]
  -- Check S is mutually relative prime.
  · rfl
  -- Check x,y are coprime.
  · simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx | hx <;>
      rcases hy with hy | hy | hy | hy <;>
        (revert ne; rw [hx, hy]; decide)
