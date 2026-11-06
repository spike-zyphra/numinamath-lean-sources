import Mathlib

theorem number_theory_191203 {x y : ℕ} (hx : x ∈ Finset.Icc 1000000 9999999) (hy : y ∈ Finset.Icc 1000000 9999999)
    (h : (1000000 * x + y) = 3 * (x * y)) :
    x = 1666667 ∧ y = 3333334 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h3 : x = 1666667 := by
    nlinarith [h, hx1, hx2, hy1, hy2]
  -- Now prove the value of Y
  have h4 : y = 3333334 := by
    rw [h3] at h
    nlinarith
  exact ⟨h3, h4⟩