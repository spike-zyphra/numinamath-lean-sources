import Mathlib

theorem algebra_215476 :
    Set.ncard {(x, y) : ℤ × ℤ | x ∈ Finset.Icc (-10) 10 ∧ y ∈ Finset.Icc (-10) 10 ∧ abs (x * y) + abs (x - y) = 2} = 4 := by 
  have h1 : {(x, y) : ℤ × ℤ | x ∈ Finset.Icc (-10) 10 ∧ y ∈ Finset.Icc (-10) 10 ∧ abs (x * y) + abs (x - y) = 2} = Finset.filter (fun p => abs (p.1 * p.2) + abs (p.1 - p.2) = 2) (Finset.Icc (-10) 10 ×ˢ Finset.Icc (-10) 10) := by
    ext ⟨x, y⟩
    simp [Finset.mem_Icc]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide