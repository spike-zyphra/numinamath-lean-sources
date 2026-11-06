import Mathlib

theorem inequalities_93159 (a b c d : ℝ) (ha : 0 < a) (hb : a < b) (hc : b < c) (hd : c < d) :
    (c + d) / (a + b) > (a + b) / (c + d) ∧
    (c + d) / (a + b) > (a + d) / (b + c) ∧
    (c + d) / (a + b) > (b + c) / (a + d) ∧
    (c + d) / (a + b) > (b + d) / (a + c) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < c + d := by linarith
  have h3 : 0 < b + c := by linarith
  have h4 : 0 < a + d := by linarith
  have h5 : 0 < a + c := by linarith

  constructor
  · -- Show that $\frac{c + d}{a + b} > \frac{a + b}{c + d}$
    have h6 : (c + d) ^ 2 > (a + b) ^ 2 := by
      nlinarith
    have h7 : (c + d) / (a + b) - (a + b) / (c + d) > 0 := by
      have h8 : 0 < (a + b) * (c + d) := by positivity
      have h9 : ((c + d) / (a + b) - (a + b) / (c + d)) = ((c + d) ^ 2 - (a + b) ^ 2) / ((a + b) * (c + d)) := by
        field_simp
        <;> ring
      rw [h9]
      apply div_pos
      linarith
      all_goals positivity
    linarith
  constructor
  · -- Show that $\frac{c + d}{a + b} > \frac{a + d}{b + c}$
    have h6 : (c + d) * (b + c) - (a + d) * (a + b) > 0 := by
      nlinarith [mul_pos ha (show 0 < b - a by linarith), mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith),
        mul_pos (show 0 < c - b by linarith) (show 0 < d - c by linarith)]
    have h7 : (c + d) / (a + b) - (a + d) / (b + c) > 0 := by
      have h8 : 0 < (a + b) * (b + c) := by positivity
      have h9 : ((c + d) / (a + b) - (a + d) / (b + c)) = ((c + d) * (b + c) - (a + d) * (a + b)) / ((a + b) * (b + c)) := by
        field_simp
        <;> ring
      rw [h9]
      apply div_pos
      linarith
      all_goals positivity
    linarith
  constructor
  · -- Show that $\frac{c + d}{a + b} > \frac{b + c}{a + d}$
    have h6 : (c + d) * (a + d) - (b + c) * (a + b) > 0 := by
      nlinarith [mul_pos ha (show 0 < b - a by linarith), mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith),
        mul_pos (show 0 < c - b by linarith) (show 0 < d - c by linarith)]
    have h7 : (c + d) / (a + b) - (b + c) / (a + d) > 0 := by
      have h8 : 0 < (a + b) * (a + d) := by positivity
      have h9 : ((c + d) / (a + b) - (b + c) / (a + d)) = ((c + d) * (a + d) - (b + c) * (a + b)) / ((a + b) * (a + d)) := by
        field_simp
        <;> ring
      rw [h9]
      apply div_pos
      linarith
      all_goals positivity
    linarith
  · -- Show that $\frac{c + d}{a + b} > \frac{b + d}{a + c}$
    have h6 : (c + d) * (a + c) - (b + d) * (a + b) > 0 := by
      nlinarith [mul_pos ha (show 0 < b - a by linarith), mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith),
        mul_pos (show 0 < c - b by linarith) (show 0 < d - c by linarith)]
    have h7 : (c + d) / (a + b) - (b + d) / (a + c) > 0 := by
      have h8 : 0 < (a + b) * (a + c) := by positivity
      have h9 : ((c + d) / (a + b) - (b + d) / (a + c)) = ((c + d) * (a + c) - (b + d) * (a + b)) / ((a + b) * (a + c)) := by
        field_simp
        <;> ring
      rw [h9]
      apply div_pos
      linarith
      all_goals positivity
    linarith