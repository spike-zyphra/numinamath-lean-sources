import Mathlib

theorem algebra_16590 {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x > y)
    (h : x + y + x * y = 80) : x = 26 := by
  have h1 : (x + 1) * (y + 1) = 81 := by
    nlinarith
  have h2 : x + 1 > 0 := by linarith
  have h3 : y + 1 > 0 := by linarith
  have h4 : x + 1 > y + 1 := by nlinarith
  have h5 : (x + 1) ∣ 81 := by
    use (y + 1)
    all_goals nlinarith
  have h6 : (x + 1) ≤ 81 := by
    apply Int.le_of_dvd (by norm_num) h5
  interval_cases h7 : (x + 1) <;> omega