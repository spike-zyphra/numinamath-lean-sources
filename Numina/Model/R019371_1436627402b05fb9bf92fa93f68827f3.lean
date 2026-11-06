import Mathlib

open Finset

theorem number_theory_113139 :
    Set.ncard {x : ℚ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2015 ∧ x = (n ^ 2 + 2) / (n ^ 2 - n + 2)} = 2014 := by
  have h1 : {x : ℚ | ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2015 ∧ x = (n ^ 2 + 2) / (n ^ 2 - n + 2)} = (Finset.image (fun (n : ℕ) => ((n ^ 2 + 2) : ℚ) / (n ^ 2 - n + 2)) (Icc 1 2015) : Set ℚ) := by
    ext x
    simp
    <;> aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide