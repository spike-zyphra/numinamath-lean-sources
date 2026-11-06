import Mathlib

theorem number_theory_12051 :
    (Finset.Icc 1 10).card * (Finset.Icc (-10) (-1)).card = 100 ∧
    {x : ℤ × ℤ | x.1 ∈ Finset.Icc 1 10 ∧ x.2 ∈ Finset.Icc (-10) (-1) ∧ 3 ∣ x.1 ^ 2 + x.2}.ncard = 37 := by
  constructor
  · -- Show that (Finset.Icc 1 10).card * (Finset.Icc (-10) (-1)).card = 100
    simp
  · -- Show that {x : ℤ × ℤ | x.1 ∈ Finset.Icc 1 10 ∧ x.2 ∈ Finset.Icc (-10) (-1) ∧ 3 ∣ x.1 ^ 2 + x.2}.ncard = 37
    have h1 : {x : ℤ × ℤ | x.1 ∈ Finset.Icc 1 10 ∧ x.2 ∈ Finset.Icc (-10) (-1) ∧ 3 ∣ x.1 ^ 2 + x.2} = Finset.filter (fun p => 3 ∣ p.1^2 + p.2) (Finset.Icc 1 10 ×ˢ Finset.Icc (-10) (-1)) := by
      ext ⟨a, b⟩
      simp
      <;> omega
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide