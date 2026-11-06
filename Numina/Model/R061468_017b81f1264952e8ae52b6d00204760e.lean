import Mathlib

theorem algebra_279157 {x y : ℕ} (hx : x ∈ Finset.Icc 1 10) (hy : y ∈ Finset.Icc 1 10) (hxy : x * y = 14) :
    x + y = 9 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  interval_cases x <;> omega