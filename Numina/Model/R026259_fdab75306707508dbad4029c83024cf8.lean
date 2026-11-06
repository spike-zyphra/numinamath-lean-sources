import Mathlib

theorem number_theory_225975 (x y z : ℕ) (hx : x ∈ Finset.Icc 1 6) (hy : y ∈ Finset.Icc 1 6)
    (hz : z ∈ Finset.Icc 1 6) (h : (10 * 10 * x + 10 * y + z) = 2 * (7 * 7 * x + 7 * y + z)) :
    (x, y, z) = (3, 1, 2) ∨ (x, y, z) = (5, 2, 2) ∨ (x, y, z) = (4, 1, 4) ∨
    (x, y, z) = (6, 2, 4) ∨ (x, y, z) = (5, 1, 6) := by
  rw [Finset.mem_Icc] at hx hy hz
  rcases hx with ⟨hx1,hx2⟩
  rcases hy with ⟨hy1,hy2⟩
  rcases hz with ⟨hz1,hz2⟩
  have h1 : x ≤ 6 := by linarith
  have h2 : y ≤ 6 := by linarith
  have h3 : z ≤ 6 := by linarith
  have h4 : x ≥ 1 := by linarith
  have h5 : y ≥ 1 := by linarith
  have h6 : z ≥ 1 := by linarith
  interval_cases x <;> interval_cases y
  <;> interval_cases z
  <;> norm_num [Prod.ext_iff] at h ⊢
  <;> tauto