import Mathlib

theorem algebra_276941 (x y : ℝ) (hx : 10 ≤ x ∧ x ≤ 20) (hy : 40 ≤ y ∧ y ≤ 60) :
    x^2 / (2 * y) ≤ 5 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : x^2 ≤ 400 := by
    nlinarith
  have h2 : y ≥ 40 := hy1
  have h3 : 2 * y > 0 := by
    nlinarith
  have h4 : x^2 ≤ 10 * y := by 
    nlinarith [h1, h2]
  have h5 : x^2 / (2 * y) ≤ 5 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  exact h5