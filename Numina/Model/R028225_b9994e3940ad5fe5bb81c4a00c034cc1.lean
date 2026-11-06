import Mathlib


theorem number_theory_278078 :
    Set.ncard {x : Finset ℕ | ∃ a b, x = {a, b} ∧ a ∈ Finset.Icc 1 100 ∧ b ∈ Finset.Icc 1 100 ∧ a ≠ b ∧ IsSquare (a * b)} = 105 := by
  have h1 : {x : Finset ℕ | ∃ a b, x = {a, b} ∧ a ∈ Finset.Icc 1 100 ∧ b ∈ Finset.Icc 1 100 ∧ a ≠ b ∧ IsSquare (a * b)} = Finset.image (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ)) (Finset.filter (fun p : ℕ × ℕ => p.1 ∈ Finset.Icc 1 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ p.1 ≠ p.2 ∧ IsSquare (p.1 * p.2)) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100)) := by
    ext x
    simp
    aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide