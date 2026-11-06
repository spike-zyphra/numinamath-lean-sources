import Mathlib

theorem algebra_272103 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 1 / (x + y) = 1 / x - 1 / y) :
    (x / y + y / x) ^ 2 = 5 := by
  have h1 : x + y > 0 := by linarith
  have h2 : x * y > 0 := by
    apply mul_pos
    all_goals linarith
  have eq1 : 1 / (x + y) = 1 / x - 1 / y := by linarith [h]
  have eq2 : x * y = y ^ 2 - x ^ 2 := by
    have eq3 : (1 / (x + y) ) = (1 / x - 1 / y) := by linarith [h]
    field_simp [(show x + y ≠ 0 by linarith), (show x ≠ 0 by linarith), (show y ≠ 0 by linarith)] at eq3
    nlinarith
  have eq3 : (y / x - x / y) = 1 := by
    have h6 : (y / x - x / y) = (y ^2 - x ^2) / (x * y) := by
      field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)]
      <;> ring
    have h7 : (y ^2 - x ^2) / (x * y) = 1 := by
      have h8 : x * y = y ^2 - x ^2 := by linarith [eq2]
      have h9 : (y ^2 - x ^2) = x * y := by linarith [h8]
      rw [h9]
      have h10 : (x * y) / (x * y) = 1 := by
        have h11 : x * y ≠ 0 := by positivity
        field_simp [h11]
      linarith [h10]
    linarith [h6, h7]
  have eq4 : (y / x - x / y) ^ 2 = 1 := by
    rw [eq3]
    norm_num
  have eq5 : (y / x) ^ 2 + (x / y) ^ 2 = 3 := by
    have eq6 : (y / x - x / y) ^ 2 = (y / x) ^ 2 - 2 + (x / y) ^ 2 := by
      field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)]
      <;> ring
    have eq7 : (y / x - x / y) ^ 2 = 1 := by linarith [eq4]
    linarith [eq6, eq7]
  have eq8 : (x / y + y / x) ^ 2 = (x / y) ^ 2 + 2 + (y / x) ^ 2 := by
    field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)]
    <;> ring
  have eq10 : (x / y + y / x) ^ 2 = 5 := by
    have h11 : (x / y + y / x) ^ 2 = (x / y) ^ 2 + 2 + (y / x) ^ 2 := by
      field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)]
      <;> ring
    have h10 : (x / y) ^ 2 + (y / x) ^ 2 = 3 := by
      linarith [eq5]
    have h12 : (x / y) ^ 2 + 2 + (y / x) ^ 2 = 5 := by
      nlinarith [h10]
    linarith [h11, h12]
  exact_mod_cast eq10