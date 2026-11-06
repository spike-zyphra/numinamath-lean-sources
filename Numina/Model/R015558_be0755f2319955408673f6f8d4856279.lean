import Mathlib

theorem algebra_326441 (u v x y : ℤ) (hu : u ∈ Set.Icc 0 11) (hv : v ∈ Set.Icc 0 11)
    (hx : x ∈ Set.Icc 0 11) (hy : y ∈ Set.Icc 0 11) (h1 : u * v - x * y = 39) (h2 : u * y - x * v = 66) :
    u = 8 ∧ v = 6 ∧ x = 1 ∧ y = 9 := by 
  rw [Set.mem_Icc] at hu hv hx hy
  rcases hu with ⟨hu0, hu11⟩
  rcases hv with ⟨hv0, hv11⟩
  rcases hx with ⟨hx0, hx11⟩
  rcases hy with ⟨hy0, hy11⟩
  interval_cases u <;> interval_cases v <;> interval_cases x <;> omega