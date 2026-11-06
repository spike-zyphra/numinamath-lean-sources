import Mathlib

theorem inequalities_602529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) / (a + c) + (a + c) / (b + c) + (b + c) / (a + b) ≤
    a / b + b / c + c / a := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc

  have h4 : a + b > 0 := by linarith
  have h5 : b + c > 0 := by linarith
  have h6 : a + c > 0 := by linarith

  have h7 : a / b + b / c + c / a = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) / (a * b * c):= by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring
  have h8 : (a + b) / (a + c) + (a + c) / (b + c) + (b + c) / (a + b) =
      ((a + b) * (b + c) * (a + b) + (a + c) * (a + b) * (a + c) + (b + c) * (a + c) * (b + c)) / ((a + c) * (b + c) * (a + b)) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring_nf

  rw [h7, h8]

  have h8 : (a * b * c) > 0 := by positivity
  have h9 : (a + c) * (b + c) * (a + b) > 0 := by positivity

  apply (div_le_div_iff (by positivity) (by positivity)).mpr

  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith),
          mul_pos (show 0 < a + b by linarith) (show 0 < a + c by linarith), mul_pos (show 0 < a + c by linarith) (show 0 < b + c by linarith)]