import Mathlib

def onlyOddDigits (n : ℕ) : Prop := 0 < n ∧ ∀ d ∈ Nat.digits 10 n, Odd d

theorem number_theory_636613 :
    IsLeast {N | ∃ p, onlyOddDigits p ∧ p ∣ N ∧ N ≠ p ∧ onlyOddDigits N} 3 := by

  constructor
  . simp
    use 1
    unfold onlyOddDigits
    simp
    decide
  . simp [lowerBounds]
    intro N p hp hpN hNp hN
    by_contra h
    simp at h
    interval_cases N
    . contrapose hN
      unfold onlyOddDigits
      simp
    . simp at hpN
      subst p
      simp at hNp
    . contrapose hN
      unfold onlyOddDigits
      simp
