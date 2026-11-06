import Mathlib

theorem algebra_12913 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 + (20:ℚ) / y - (101:ℚ) / x = (2043:ℚ) / (x * y)) :
    x + y = 105 := by
  have h1 : (x : ℚ) > 0 := by exact_mod_cast hx
  have h2 : (y : ℚ) > 0 := by exact_mod_cast hy
  have h3 : (x * y : ℚ) + (20 * x : ℚ) - (101 * y : ℚ) = (2043 : ℚ) := by
    have h4 : (x * y : ℚ) > 0 := by positivity
    have eq1 : (1 + (20 : ℚ) / y - (101 : ℚ) / x) * (x * y) = (2043 : ℚ) := by
      rw [h]
      <;> field_simp [(show (x : ℚ) ≠ 0 by positivity), (show (y : ℚ) ≠ 0 by positivity)]
    have eq2 : (1 + (20 : ℚ) / y - (101 : ℚ) / x) * (x * y) =
        (x * y : ℚ) + (20 * x : ℚ) - (101 * y : ℚ) := by
      field_simp [(show (x : ℚ) ≠ 0 by positivity), (show (y : ℚ) ≠ 0 by positivity)]
      <;> ring
    rw [eq2] at eq1
    linarith
  have h4 : x * y + 20 * x - 101 * y = 2043 := by
    have h5 : (x * y : ℚ) + (20 * x : ℚ) - (101 * y : ℚ) = (2043 : ℚ) := h3
    have h6 : (x * y + 20 * x - 101 * y : ℚ) = (2043 : ℚ) := by
      linarith
    have h7 : (x * y + 20 * x - 101 * y : ℤ) = (2043 : ℤ) := by
      exact_mod_cast h6
    linarith
  have h6 : (x - 101) * (y + 20) = 23 := by
    nlinarith [h4]
  have h7 : (x - 101) ∣ 23 := by
    use y + 20
    all_goals linarith [h6]
  have h8 : (x - 101) ≤ 23 := by
    apply Int.le_of_dvd (by norm_num) h7
  have h9 : (x - 101) ≥ -23 := by
    have h10 : -(x - 101) ∣ 23 := by
      exact Int.neg_dvd.2 h7
    have h11 : -(x - 101) ≤ 23 := by
      apply Int.le_of_dvd (by norm_num) h10
    linarith
  have h10 : (x - 101) = 1 ∨ (x - 101) = 23 ∨ (x - 101) = -1 ∨ (x - 101) = -23 := by
    interval_cases h : x - 101 <;> tauto
  rcases h10 with (h10 | h10 | h10 | h10)
  · -- Case 1: x - 101 = 1
    have hx' : x = 102 := by linarith
    have hy' : y = 3 := by
      nlinarith [h6, h10]
    linarith [hx', hy']
  · -- Case 2: x - 101 = 23
    have hx' : x = 124 := by linarith
    have hy' : y = -19 := by 
      nlinarith [h6, h10]
    linarith [show y ≥ 0 from by linarith, show y < 0 from by nlinarith]
  · -- Case 3: x - 101 = -1
    have hx' : x = 100 := by linarith
    have hy' : y = -43 := by 
      nlinarith [h6, h10]
    linarith [show y ≥ 0 from by linarith, show y < 0 from by nlinarith]
  · -- Case 4: x - 101 = -23
    have hx' : x = 78 := by linarith
    have hy' : y = -21 := by 
      nlinarith [h6, h10]
    linarith [show y ≥ 0 from by linarith, show y < 0 from by nlinarith]