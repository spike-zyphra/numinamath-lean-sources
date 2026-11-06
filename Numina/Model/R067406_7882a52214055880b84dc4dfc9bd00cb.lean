import Mathlib

theorem number_theory_108552 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x * 100 + y ≡ 0 [ZMOD x * y]) :
    x = 17 ∧ y = 34 ∨ x = 13 ∧ y = 52 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  norm_num [Int.ModEq] at hxy
  interval_cases x <;> interval_cases y <;> norm_num at hxy ⊢ <;> omega