import Mathlib

/- Definition of mutually relative prime, same as in Problem 4517 and 4520. -/
def MutuallyRelativePrime1 (s : Finset ℕ) := s.gcd id = 1

/- The solution set. -/
def S : Finset ℕ := {6, 10, 15}

/- Find a set of three integers that are mutually relatively prime, meaning that
  the greatest common divisor (GCD) of any two integers in the set is greater than 1,
  but the GCD of the entire set is 1. Additionally, the integers should not be pairwise relatively prime,
  meaning that at least one pair of integers shares a common factor greater than 1. -/
theorem number_theory_4518 :
    S.card = 3 ∧ MutuallyRelativePrime1 S ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬Nat.Coprime x y := by
  refine ⟨?_, ?_, fun x hx y hy ne => ?_⟩
  -- Check S.card=3 .
  · simp [S]
  -- Check S is mutually relative prime.
  · rfl
  -- Check x,y are not coprime.
  · simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx <;>
      rcases hy with hy | hy | hy <;>
        (revert ne; rw [hx, hy]; decide)
