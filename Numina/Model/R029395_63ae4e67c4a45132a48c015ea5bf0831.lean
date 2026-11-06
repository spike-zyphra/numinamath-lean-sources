import Mathlib

theorem number_theory_236161 :
    Set.ncard {p : ℤ × ℤ | p.1 ∈ Finset.Icc 1 1000 ∧ p.2 ∈ Finset.Icc 1 1000 ∧ 7 ∣ p.1^2 + p.2^2} = 20164 := by
  have h1 : {p : ℤ × ℤ | p.1 ∈ Finset.Icc 1 1000 ∧ p.2 ∈ Finset.Icc 1 1000 ∧ 7 ∣ p.1^2 + p.2^2} = Finset.filter (fun p : ℤ × ℤ => 7 ∣ p.1^2 + p.2^2) (Finset.Icc 1 1000 ×ˢ Finset.Icc 1 1000 : Finset (ℤ × ℤ)) := by 
    ext ⟨x, y⟩
    simp [Finset.mem_Icc]
    <;> try { tauto }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide