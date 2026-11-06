import Mathlib

theorem algebra_270062 (x : ℝ) (hx : x ≠ 7 / 8 ∧ x ≠ 4 / 5 ∧ x ≠ 1 / 2) :
    (306 * x ^ 2 - 450 * x + 162) / ((8 * x - 7) * (5 * x - 4) * (2 * x - 1)) =
    9 / (8 * x - 7) + 6 / (5 * x - 4) + 3 / (2 * x - 1) := by
  rcases hx with ⟨hx1, hx2, hx3⟩
  have h1 : 8 * x - 7 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h2 : 5 * x - 4 ≠ 0 := by
    intro h
    apply hx2
    linarith
  have h3 : 2 * x - 1 ≠ 0 := by
    intro h
    apply hx3
    linarith
  have h1' : 8 * x - 7 ≠ 0 := h1
  have h2' : 5 * x - 4 ≠ 0 := h2
  have h3' : 2 * x - 1 ≠ 0 := h3
  field_simp [(show 8 * x - 7 ≠ 0 by assumption), (show 5 * x - 4 ≠ 0 by assumption), 
    (show 2 * x - 1 ≠ 0 by assumption)]
  ring_nf