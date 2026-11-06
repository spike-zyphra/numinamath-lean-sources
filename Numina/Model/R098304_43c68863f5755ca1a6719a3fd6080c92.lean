import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_306560 (x : ℝ) (hx : 0 < x ∧ x < 1)
  (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
  a^2 / x + b^2 / (1 - x) ≥ (a + b)^2 := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 < x := hx1
  have h2 : x < 1 := hx2
  have h3 : 1 - x > 0 := by linarith
  have h4 : a^2 / x + b^2 / (1 - x) - (a + b) ^ 2 ≥ 0 := by
    have pos1 : x * (1 - x) > 0 := mul_pos hx1 (by linarith)
    have h5 : a^2 / x + b^2 / (1 - x) - (a + b) ^ 2 =
      ( ((a + b) * x - a) ^ 2 ) / (x * (1 - x)) := by
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
      <;> field_simp
      <;> nlinarith [sq_nonneg ((a + b) * x - a), sq_nonneg (a - b), sq_nonneg (x - a / (a + b)), sq_nonneg (x - 1 / 2)]
    rw [h5]
    have h7 : ( ((a + b) * x - a) ^ 2 ) / (x * (1 - x)) ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg ((a + b) * x - a)
      · positivity
    linarith
  linarith