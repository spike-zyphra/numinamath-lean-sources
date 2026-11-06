import Mathlib

/- 1. Find all natural numbers such that if you add their smallest divisor greater than one to them, the result is 30. -/
theorem number_theory_105648 (n : ℕ) (hn : 1 < n) :
    n + n.primeFactorsList.head! = 30 ↔ n = 25 ∨ n = 27 ∨ n = 28 :=
by
  constructor; swap
  . -- The first direction is trivial.
    rintro (h|h|h) <;> subst h
    . simp [Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
      decide
    . simp [Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
      decide
    . simp [Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
      decide
  . intro eq
    have : n ≤ 30 := by linarith
    have : n ∈ List.range' 2 29 := by
      simp
      constructor <;> linarith
    simp only [List.range'] at this
    -- 30 is small, we can try each one of them.
    repeat (
      rcases this with (h|this);
      simp [Nat.primeFactorsList, Nat.minFac, Nat.minFacAux] at eq; 
      try tauto
    )
    