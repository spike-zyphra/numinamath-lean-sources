import Mathlib

def isGood (n : ℕ) : Prop :=
  ∀ i, i < (Nat.digits 10 n).length → (Nat.digits 10 n)[i]! - (Nat.digits 10 n)[i + 1]! ≥ 5

theorem number_theory_250765 (n : ℕ) (h₀ : n = 74) :
    ¬isGood n := by 
  rw [h₀]
  intro h
  specialize h 0 (by norm_num)
  norm_num [Nat.digits, Nat.digitsAux] at h