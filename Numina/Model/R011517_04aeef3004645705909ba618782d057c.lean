import Mathlib

theorem number_theory_626808 (A B C D E : ℕ) (hA : 1 ≤ A ∧ A ≤ 9) (hB : 0 ≤ B ∧ B ≤ 9) (hC : 1 ≤ C ∧ C ≤ 9) (hD : 0 ≤ D ∧ D ≤ 9) (hE : 0 ≤ E ∧ E ≤ 9) (h : (A * 10 + B) * (C * 100 + D * 10 + E) * 6 = (A * 10000 + B * 1000 + C * 100 + D * 10 + E)) : A * 10000 + B * 1000 + C * 100 + D * 10 + E = 21168 := by
  have h1 : A ≤ 9 := hA.right
  have h2 : 1 ≤ A := hA.left
  have h3 : B ≤ 9 := hB.right
  have h4 : 0 ≤ B := hB.left
  have h5 : C ≤ 9 := hC.right
  have h6 : 1 ≤ C := hC.left
  have h7 : D ≤ 9 := hD.right
  have h8 : 0 ≤ D := hD.left
  have h9 : E ≤ 9 := hE.right
  have h10 : 0 ≤ E := hE.left
  interval_cases A <;> interval_cases B <;> interval_cases C <;> omega