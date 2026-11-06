import Mathlib

theorem number_theory_124426 :
    Set.ncard {x : Finset ℕ | ∃ a b, x = {a, b} ∧ a ≠ b ∧ (a * b) % 5 = 1 ∧ a ∈ Finset.Icc 1 100 ∧ b ∈ Finset.Icc 1 100} = 780 := by
  have h1 : {x : Finset ℕ | ∃ a b, x = {a, b} ∧ a ≠ b ∧ (a * b) % 5 = 1 ∧ a ∈ Finset.Icc 1 100 ∧ b ∈ Finset.Icc 1 100} = Finset.image (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ)) (Finset.filter (fun p : ℕ × ℕ => p.1 ≠ p.2 ∧ (p.1 * p.2) % 5 = 1) (Finset.Icc (1 : ℕ) 100 ×ˢ Finset.Icc (1 : ℕ) 100)) := by
    ext x
    simp
    <;> aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide