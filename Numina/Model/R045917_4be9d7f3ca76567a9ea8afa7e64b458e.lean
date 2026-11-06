import Mathlib

theorem algebra_297286 {x y u v : ℤ} (hx : x ∈ Set.Icc 0 11) (hy : y ∈ Set.Icc 0 11)
    (hu : u ∈ Set.Icc 0 11) (hv : v ∈ Set.Icc 0 11) (f : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hf : ∀ a b c d, f a b c d = a * b - c * d) (huv : f u v x y = 39) (hxy : f u y x v = 66) :
    x = 1 ∧ y = 9 ∧ u = 8 ∧ v = 6 := by
  rw [hf] at huv hxy
  rcases hx with ⟨hx0, hx11⟩
  rcases hy with ⟨hy0, hy11⟩
  rcases hu with ⟨hu0, hu11⟩
  rcases hv with ⟨hv0, hv11⟩
  have h1 : u * v - x * y = 39 := by 
    linarith
  have h2 : u * y - x * v = 66 := by
    linarith
  interval_cases u <;> interval_cases v <;> interval_cases x <;> omega