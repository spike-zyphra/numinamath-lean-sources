import Mathlib

theorem number_theory_112943 (x y z : ℕ) (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x ≠ y) (hz : z ∈ Finset.Icc 100 999) (hxy1 : y = 10 * (x % 10) + (x / 10)) (hxy2 : x * y = z)
    (hxy3 : (z / 100) % 10 = z % 10) :
    (x = 21 ∧ y = 12 ∧ z = 252) ∨ (x = 12 ∧ y = 21 ∧ z = 252) := by
  rw [Finset.mem_Icc] at hx hy hz
  rcases hx with ⟨hx10, hx99⟩
  rcases hy with ⟨hy10, hy99⟩
  rcases hz with ⟨hz100, hz999⟩
  interval_cases x <;> norm_num [hxy1] at hxy hxy1 hxy2 hxy3 ⊢
  <;> omega