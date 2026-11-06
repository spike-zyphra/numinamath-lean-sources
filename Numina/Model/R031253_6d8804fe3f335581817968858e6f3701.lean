import Mathlib

theorem inequalities_66443 {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (hord : a ≥ b ∧ b ≥ c) :
    (a - b + c) * (1 / a - 1 / b + 1 / c) ≥ 1 := by
  rcases hord with ⟨hab, hbc⟩
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  
  have h4 : a ≥ b := hab
  have h5 : b ≥ c := hbc
  
  have h6 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
  
  have h9 : (a - b + c) * (1 / a - 1 / b + 1 / c) - 1 ≥ 0 := by
    have h10 : (a - b + c) * (1 / a - 1 / b + 1 / c) - 1 =
      ((a - b + c) * (b * c - a * c + a * b) - a * b * c) / (a * b * c) := by
      have h11 : a ≠ 0 := by linarith
      have h12 : b ≠ 0 := by linarith
      have h13 : c ≠ 0 := by linarith
      field_simp
      ring_nf
      <;> field_simp
      <;> ring
    rw [h10]
    have h14 : (a - b + c) * (b * c - a * c + a * b) - a * b * c ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - c),
        mul_nonneg (show a - b ≥ 0 by linarith) (show b - c ≥ 0 by linarith),
        mul_nonneg (show b - c ≥ 0 by linarith) (show 0 ≤ c by linarith),
        mul_nonneg (show a - c ≥ 0 by linarith) (show 0 ≤ c by linarith),
        sq_nonneg (a * b - a * c + b * c),
        sq_nonneg (a * (b - c)), sq_nonneg (c * (a - b)), sq_nonneg ((a - c) * (a - b))]
    apply div_nonneg
    linarith
    positivity
  
  linarith
  all_goals positivity