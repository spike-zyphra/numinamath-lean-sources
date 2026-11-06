import Mathlib

theorem algebra_272662 (x y : ℝ) (hx : -4 ≤ x ∧ x ≤ -2) (hy : 2 ≤ y ∧ y ≤ 4) :
    (x + y) / x ≤ 1 / 2 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : x < 0 := by
    linarith
  have h2 : (x + y) / x ≤ 1 / 2 := by
    have h3 : x < 0 := h1
    apply (div_le_iff_of_neg' (by linarith)).mpr
    nlinarith
  exact h2