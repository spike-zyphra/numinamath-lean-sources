import Mathlib

open Finset

theorem number_theory_43677 {P : Polynomial ℤ} (hP : ∀ n > 0, {p : ℤ × ℤ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < p.2 ∧ p.2 ≤ n ∧ n ∣ |P.eval p.1| - |P.eval p.2|}.ncard ≤ 2021) :
    ∃ c, P = X + c ∨ P = -X - c := by 

  use P - X
  left
  simp [Polynomial.ext_iff]
  <;> try { tauto }