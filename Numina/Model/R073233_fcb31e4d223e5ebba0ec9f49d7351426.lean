import Mathlib

theorem algebra_836 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * 3 = b * 2 ∧ b * 4 = c * 3) (h1 : 0 < (a * 0.25 + b * 0.1 + c * 0.2)) (h2 : 0 < (a + b + c)):
    (a * 0.25 + b * 0.1 + c * 0.2) / (a + b + c) = 8 / 45 := by
  rcases h with ⟨ha1, hb1⟩
  have ha2 : a = (2 / 3) * b := by
    linarith
  have hc2 : c = (4 / 3) * b := by
    linarith
  have total_original : a + b + c = 3 * b := by
    rw [ha2, hc2]
    linarith
  have total_compressed : a * 0.25 + b * 0.1 + c * 0.2 = (8 / 15) * b := by
    rw [ha2, hc2]
    ring_nf
    <;> linarith
  have hb' : b ≠ 0 := by
    by_contra h
    rw [h] at total_compressed
    nlinarith [h1, show 0 < b by linarith]
  rw [total_compressed, total_original]
  field_simp [show b ≠ 0 by assumption]
  <;> ring_nf <;> nlinarith