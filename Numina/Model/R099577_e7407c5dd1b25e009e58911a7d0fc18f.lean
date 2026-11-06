import Mathlib

theorem algebra_70878 {a b c : ℝ} (ha : a < b) (hb : b < c)
    (f : ℝ → ℝ)
    (hf : f = fun x => c * (x - a) * (x - b) / ((c - a) * (c - b)) +
      a * (x - b) * (x - c) / ((a - b) * (a - c)) +
      b * (x - c) * (x - a) / ((b - c) * (b - a))) :
    f 2014 = 2014 := by
  rw [hf]
  have ha1 : a - b ≠ 0 := by linarith
  have ha2 : a - c ≠ 0 := by linarith
  have hb1 : b - c ≠ 0 := by linarith
  have hb2 : b - a ≠ 0 := by linarith
  have hc1 : c - a ≠ 0 := by linarith
  have hc2 : c - b ≠ 0 := by linarith
  field_simp [ha1, ha2, hb1, hb2, hc1, hc2]
  ring