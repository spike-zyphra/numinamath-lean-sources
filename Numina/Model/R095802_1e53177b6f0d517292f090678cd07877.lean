import Mathlib

theorem algebra_306 {a b c : ℝ} (h : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    (b - c) / ((a - b) * (a - c)) + (c - a) / ((b - c) * (b - a)) +
    (a - b) / ((c - a) * (c - b)) + 2 / (b - a) - 2 / (c - a) = 2 / (b - c) := by 
  rcases h with ⟨ha1, hb1, ha2⟩
  have h1 : a - b ≠ 0 := by intro h0; apply ha1; linarith
  have h2 : b - c ≠ 0 := by intro h0; apply hb1; linarith
  have h3 : a - c ≠ 0 := by intro h0; apply ha2; linarith
  have h4 : b - a ≠ 0 := by intro h0; apply ha1; linarith
  have h5 : c - a ≠ 0 := by intro h0; apply ha2; linarith
  have h6 : c - b ≠ 0 := by intro h0; apply hb1; linarith
  field_simp [h1, h2, h3, h4, h5, h6]
  <;> ring_nf <;> field_simp [h1, h2, h3, h4, h5, h6] <;> ring