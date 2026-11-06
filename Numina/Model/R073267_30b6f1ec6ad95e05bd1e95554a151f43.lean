import Mathlib

theorem algebra_134321 {x y : ℕ} (hx : x ∈ Finset.Icc 100 999) (hy : y ∈ Finset.Icc 100 999)
    (h : 1000 * x + y = 7 * (x * y)) :
    x = 143 ∧ y = 143 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  interval_cases x <;> omega