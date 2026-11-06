import Mathlib

theorem number_theory_3710 :
    Set.ncard {p : ℤ × ℤ | p.1 ∈ Finset.Icc (-2) 6 ∧ p.2 ∈ Finset.Icc (-3) 5 ∧ 0 < p.1 * p.2 ∧ p.1 * p.2 ≤ 11} = 24 := by
  have h1 : {p : ℤ × ℤ | p.1 ∈ Finset.Icc (-2) 6 ∧ p.2 ∈ Finset.Icc (-3) 5 ∧ 0 < p.1 * p.2 ∧ p.1 * p.2 ≤ 11} = Finset.filter (fun p => 0 < p.1 * p.2 ∧ p.1 * p.2 ≤ 11) (Finset.Icc (-2) 6 ×ˢ Finset.Icc (-3) 5) := by
    ext ⟨x, y⟩
    simp [Finset.mem_Icc]
    <;> omega

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide