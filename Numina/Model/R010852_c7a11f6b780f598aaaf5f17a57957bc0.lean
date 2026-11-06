import Mathlib

theorem algebra_16315 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x * y = 3774) : min x y = 51 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  interval_cases x <;> omega