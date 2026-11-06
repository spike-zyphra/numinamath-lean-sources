import Mathlib

theorem algebra_254792 (A P M F : ℕ) (hA : A + 2 = P - 2) (hP : P - 2 = 2 * M) (hM : 2 * M = F / 2)
    (h : A + P + M + F = 90) :
    A = 18 ∧ P = 22 ∧ M = 10 ∧ F = 40 := by
  have h1 : P = A + 4 := by
    omega
  have h3 : P = 2 * M + 2 := by
    omega
  have h4 : A = 2 * M - 2 := by
    omega
  have h5 : F = 4 * M := by
    have h6 : F = 4 * M := by
      omega
    omega
  have h6 : 9 * M = 90 := by
    omega
  have h7 : M = 10 := by
    omega
  have h8 : A = 18 := by
    omega
  have h9 : P = 22 := by
    omega
  have h10 : F = 40 := by
    omega
  exact ⟨h8, h9, h7, h10⟩