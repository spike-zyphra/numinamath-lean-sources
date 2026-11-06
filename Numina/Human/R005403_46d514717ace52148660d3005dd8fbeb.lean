import Mathlib

open Finset

def S: Finset (ℕ × ℕ × ℕ) := (Icc 1 17 ×ˢ Icc 1 17 ×ˢ Icc 1 17).filter (fun (i, j, k) => i + j + k = 17)

/- Let S denote the set of all triples 
(i,j,k) of positive integers where i+j+k=17. Compute
∑(i,j,k)∈S, ijk -/

theorem combinatorics_608160: 
  ∑ x ∈ S, x.1 * x.2.1 * x.2.2 = 11628 := by

  simp [S]
  native_decide