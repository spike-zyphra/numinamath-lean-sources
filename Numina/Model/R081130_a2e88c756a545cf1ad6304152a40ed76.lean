import Mathlib

theorem algebra_168563 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y = (2 / 5) * x) :
    (x - y) / x = 60 / 100 ∧ (x + y) / x = 140 / 100 := by 
  have h1 : (x - y) / x = 60 / 100 := by
    rw [h]
    have h2 : x ≠ 0 := hx
    field_simp [h2]
    ring_nf
  have h3 : (x + y) / x = 140 / 100 := by 
    rw [h]
    have h4 : x ≠ 0 := hx
    field_simp [h4]
    ring_nf
  exact ⟨h1, h3⟩