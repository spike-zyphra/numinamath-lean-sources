import Mathlib

open Real

theorem number_theory_188451 (x y : ℕ) (hx : x ∈ Finset.Icc 1 8) (hy : y ∈ Finset.Icc 1 8)
    (h : sqrt (x * 10 ^ (Nat.digits 10 x).length) = y * 10 ^ (Nat.digits 10 y).length) :
    (x, y) = (1, 3) ∨ (x, y) = (4, 6) ∨ (x, y) = (6, 4) := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  interval_cases x <;> interval_cases y <;> norm_num [Real.sqrt_eq_iff_sq_eq] at h <;> tauto