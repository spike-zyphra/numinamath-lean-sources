import Mathlib

theorem number_theory_152637 (A : ℕ) (hA : A > 0) (B C D : ℕ)
    (hB : 10 > A ∧ A > B ∧ B > C ∧ C > D ∧ D > 0)
    (hC : 1000 * A + 100 * B + 10 * C + D - (D * 1000 + C * 100 + B * 10 + A) =
    B * 1000 + D * 100 + A * 10 + C) :
    B + C + D = 11 := by

  have h1 : 10 > A := hB.1
  have h2 : A > B := hB.2.1
  have h3 : B > C := hB.2.2.1
  have h4 : C > D := hB.2.2.2.1
  have h5 : D > 0 := hB.2.2.2.2

  have h6 : 1000 * A + 100 * B + 10 * C + D ≥ D * 1000 + C * 100 + B * 10 + A := by 
    omega

  have h7 : 1000 * A + 100 * B + 10 * C + D - (D * 1000 + C * 100 + B * 10 + A) = B * 1000 + D * 100 + A * 10 + C := by 
    omega

  have h8 : A ≤ 9 := by omega
  have h9 : B ≤ 9 := by omega
  have h10 : C ≤ 9 := by omega
  have h11 : D ≤ 9 := by omega

  interval_cases A <;> interval_cases B <;> interval_cases C <;> omega