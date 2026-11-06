import Mathlib

theorem algebra_13887 : IsGreatest {(y) | (x : ℤ) (y : ℤ) (_ : x * y + 5 * x + 4 * y = -5)} 10 := by
  constructor
  · -- Show that 10 is in the set.
    use -3, 10
    all_goals norm_num
  · -- Show that any y in the set ≤ 10.
    intro y 
    intro hy
    rcases hy with ⟨x, y, h, rfl⟩
    have eq1 : (x + 4) * (y + 5) = 15 := by
      nlinarith
    have h1 : (y + 5) ∣ 15 := by
      use x + 4
      all_goals linarith
    -- From the fact that `y + 5` divides 15, we need to show that y ≤ 10.
    -- The possible values of (y + 5) are × = ÷3  ×  4  3  × 5 × 0  v3  v4  × 4  6  4  × 5  4  4  5  4  5  4  9  7  9  2 =  -1 -3 -5 -15 1 3 5 15.
    -- From each of these cases, we show y ≤ 10.
    have h4 : y ≤ 10 := by
      have h10 : (y + 5) ∣ 15 := h1 
      have h100 : (y + 5) ≤ 15 := by
        exact Int.le_of_dvd (by norm_num) h10 
      have h101 : (y + 5) ≥ -15 := by
        have h102 : -(y + 5) ∣ 15 := by
          exact Int.neg_dvd.2 h10 
        have h103 : -(y + 5) ≤ 15 := by
          apply Int.le_of_dvd (show 0 < 15 by norm_num) h102 
        omega 
      interval_cases h103 : (y + 5) <;> omega 
    linarith