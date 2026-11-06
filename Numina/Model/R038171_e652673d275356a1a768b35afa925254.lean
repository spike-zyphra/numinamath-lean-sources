import Mathlib

theorem algebra_287837 (x : ℝ) (hx : x ≠ 3 / 2 ∧ 18 * x ^ 4 - 63 * x ^ 3 + 22 * x ^ 2 + 112 * x - 96 ≠ 0) :
    (18 * x ^ 4 - 9 * x ^ 3 - 86 * x ^ 2 + 16 * x + 96) / (18 * x ^ 4 - 63 * x ^ 3 + 22 * x ^ 2 + 112 * x - 96) =
    (2 * x + 3) / (2 * x - 3) := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 2 * x - 3 ≠ 0 := by 
    intro h
    have h2 : x = 3 / 2 := by linarith 
    tauto 
  have h3 : 18 * x ^ 4 - 63 * x ^ 3 + 22 * x ^ 2 + 112 * x - 96 ≠ 0 := hx2
  field_simp [h3, h1]
  ring_nf
  <;> nlinarith