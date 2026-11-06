import Mathlib

theorem number_theory_174908 : Set.ncard {N : ℕ | N ∈ Finset.Icc 10 99 ∧ IsSquare (N + (N % 10) * 10 + N / 10)} = 8 := by
  have h1 : {N : ℕ | N ∈ Finset.Icc 10 99 ∧ IsSquare (N + (N % 10) * 10 + N / 10)} = 
      (Finset.Icc 10 99).filter (fun n => IsSquare (n + (n % 10) * 10 + n / 10)) := by 
    ext N
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide