import Mathlib

open Real
open scoped BigOperators

theorem inequalities_9942 :
  Set.ncard {p : ℤ × ℤ | p.1 ∈ Finset.Icc (-10) 10 ∧ p.2 ∈ Finset.Icc (-10) 10 ∧
    (abs p.1 - 1)^2 + (abs p.2 - 1)^2 < 2} = 16 := by
  have h1 : {p : ℤ × ℤ | p.1 ∈ Finset.Icc (-10) 10 ∧ p.2 ∈ Finset.Icc (-10) 10 ∧
    (abs p.1 - 1)^2 + (abs p.2 - 1)^2 < 2} = Finset.filter (fun p => (abs p.1 - 1)^2 + (abs p.2 - 1)^2 < 2) (Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10 : ℤ) 10) := by
    ext ⟨x, y⟩
    simp [Finset.mem_Icc]
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide