import Mathlib

theorem inequalities_310346 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    25 < (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) := by
  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < c + a := by nlinarith
  have h3 : 0 < a + b := by nlinarith
  have h4 : (1 + 4 * a / (b + c)) = (4 * a + b + c) / (b + c) := by
    field_simp
    <;> ring
    <;> field_simp
  have h5 : (1 + 4 * b / (c + a)) = (4 * b + c + a) / (c + a) := by
    field_simp
    <;> ring
    <;> field_simp
  have h6 : (1 + 4 * c / (a + b)) = (4 * c + a + b) / (a + b) := by
    field_simp
    <;> ring
    <;> field_simp
  rw [h4, h5, h6]
  have eq1 : ((4 * a + b + c) / (b + c)) * ((4 * b + c + a) / (c + a)) * ((4 * c + a + b) / (a + b)) = (4 * a + b + c) * (4 * b + c + a) * (4 * c + a + b) / ((b + c) * (c + a) * (a + b)) := by
    field_simp
    <;> ring
    <;> field_simp
  rw [eq1]
  have h7_pos : 0 < (b + c) * (c + a) * (a + b) := by positivity
  have h8 : (4 * a + b + c) * (4 * b + c + a) * (4 * c + a + b) > 25 * (b + c) * (c + a) * (a + b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < b + c by nlinarith) (show 0 < c + a by nlinarith), 
      mul_pos (show 0 < b + c by nlinarith) (show 0 < a + b by nlinarith), 
      mul_pos (show 0 < c + a by nlinarith) (show 0 < a + b by nlinarith)]
  have h9 : ( (4 * a + b + c) * (4 * b + c + a) * (4 * c + a + b) ) / ((b + c) * (c + a) * (a + b)) > (25 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
    apply (div_lt_div_right (by positivity)).mpr
    linarith
  have h10 : (25 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) = 25 := by
    field_simp
    <;> ring_nf <;> field_simp <;> ring
    <;> positivity
  have h11 : ( (4 * a + b + c) * (4 * b + c + a) * (4 * c + a + b) ) / ((b + c) * (c + a) * (a + b)) > 25 := by
    linarith [h9, h10]
  linarith