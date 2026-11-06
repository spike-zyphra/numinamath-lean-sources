import Mathlib

theorem algebra_15105 {x y : ℤ} (hx : 1 < x) (hy : 1 < y)
    (h : (2 * x + 3) * (y + 2) - x * y = 34) :
    x * y = 8 := by
  have h1 : x * y + 4 * x + 3 * y = 28 := by
    nlinarith
  have h2 : (x + 3) * (y + 4) = 40 := by
    linarith [h1]
  have h3 : x + 3 ∣ 40 := by
    use y + 4
    all_goals linarith [h2]
  have h4 : x + 3 ∣ 40 := h3
  have h5 : x + 3 ≤ 40 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h6 : x + 3 ≥ 5 := by 
    omega
  interval_cases h7 : x + 3 <;> omega 
  all_goals
    omega