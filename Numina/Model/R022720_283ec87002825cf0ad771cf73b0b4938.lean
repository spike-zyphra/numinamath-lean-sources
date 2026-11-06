import Mathlib

open Real

theorem inequalities_994 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ^ 2 ≤ 27 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  have ha3 : 0 < a := by linarith
  have hb3 : 0 < b := by linarith
  have hc3 : 0 < c := by linarith
  have h1 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp
    <;> ring

  have h2 : (a + b + c) * (1 / a + 1 / b + 1 / c) ^ 2 = (a + b + c) * ((b * c + a * c + a * b) / (a * b * c)) ^ 2 := by
    rw [h1]

  have h3 : (a + b + c) * ((b * c + a * c + a * b) / (a * b * c)) ^ 2 = (a + b + c) * ((b * c + a * c + a * b) ^ 2) / ((a * b * c) ^ 2) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring_nf

  rw [h2, h3]

  have h4 : (a + b + c) * ((b * c + a * c + a * b) ^ 2) ≤ 27 * ((a * b * c) ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (a - 1) by linarith) (show (0 : ℝ) ≤ (b - 1) by linarith)) (show (0 : ℝ) ≤ (c - 1) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (a - 1) by linarith) (show (0 : ℝ) ≤ (b - 1) by linarith)) (show (0 : ℝ) ≤ (2 - c) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (a - 1) by linarith) (show (0 : ℝ) ≤ (2 - b) by linarith)) (show (0 : ℝ) ≤ (c - 1) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (a - 1) by linarith) (show (0 : ℝ) ≤ (2 - b) by linarith)) (show (0 : ℝ) ≤ (2 - c) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (2 - a) by linarith) (show (0 : ℝ) ≤ (b - 1) by linarith)) (show (0 : ℝ) ≤ (c - 1) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (2 - a) by linarith) (show (0 : ℝ) ≤ (b - 1) by linarith)) (show (0 : ℝ) ≤ (2 - c) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (2 - a) by linarith) (show (0 : ℝ) ≤ (2 - b) by linarith)) (show (0 : ℝ) ≤ (c - 1) by linarith), 
          mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (2 - a) by linarith) (show (0 : ℝ) ≤ (2 - b) by linarith)) (show (0 : ℝ) ≤ (2 - c) by linarith), 
          sq_nonneg (a + b + c - 3), 
          sq_nonneg (a * b + b * c + c * a - 3), 
          mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ b - 1 by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith)]

  have h5 : (a * b * c) ^ 2 > 0 := by
    positivity
  apply (div_le_iff₀ h5).mpr
  nlinarith [h4]