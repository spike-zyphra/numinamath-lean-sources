import Mathlib

def sumOfAges (a b c : ℕ) : ℕ := a + b + c

def sumOfAgesInThreeYears (a b c : ℕ) : ℕ := a + 3 + b + 3 + c + 3

theorem algebra_234572 (a b c : ℕ) (h₀ : sumOfAges a b c = 31) :
    sumOfAgesInThreeYears a b c = 40 := by
  simp [sumOfAges, sumOfAgesInThreeYears] at h₀ ⊢
  omega