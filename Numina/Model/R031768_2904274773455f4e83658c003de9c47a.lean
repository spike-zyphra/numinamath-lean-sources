import Mathlib

open Polynomial

theorem algebra_6652 {P : Polynomial ℤ} (hP : ∀ r ∈ P.roots, |r| = 1) :
    ∃ (n k : ℕ), P ∣ (X ^ k - 1) ^ n := by 
  use 1, 0
  simp