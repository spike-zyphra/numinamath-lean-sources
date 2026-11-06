import Mathlib

theorem number_theory_639169 (Q : ℕ) (hQ : Q > 0) (M : ℕ → ℕ)
  (hM0 : M 0 = 0) (hM : ∀ i : ℕ, M (i + 1) = 2 * M i + Q) :
  ∀ k : ℕ, M k = Q * (2 ^ k - 1) := by 
  intro k
  induction k with
  | zero =>
    rw [hM0]
    simp
  | succ k ih =>
    rw [hM, ih]
    zify at *
    have cast1 : ↑(2 ^ k - 1 : ℕ) = (2 ^ k - (1 : ℤ)) := by 
      have ge1 : 2 ^ k ≥ 1 := by 
        exact Nat.one_le_two_pow 
      norm_cast
    have cast2 : ↑(2 ^ (k + 1) - 1 : ℕ) = (2 ^ (k + 1)- (1 : ℤ)) := by 
      have ge1 : 2 ^ (k + 1) ≥ 1 := by 
        exact Nat.one_le_two_pow
      norm_cast
    rw [cast1, cast2]
    ring_nf
