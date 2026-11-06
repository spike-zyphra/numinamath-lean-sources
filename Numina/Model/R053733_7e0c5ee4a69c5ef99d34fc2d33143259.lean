import Mathlib

theorem number_theory_110165 : {p : ℤ × ℤ | p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ 7 * p.1 + 11 * p.2 ≤ 77}.ncard = 49 := by
  have h1 : {p : ℤ × ℤ | p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ 7 * p.1 + 11 * p.2 ≤ 77} = Finset.filter (fun p => p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ 7 * p.1 + 11 * p.2 ≤ 77) (Finset.Icc (-100 : ℤ) 100 ×ˢ Finset.Icc (-100 : ℤ) 100) := by
    ext ⟨x, y⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide