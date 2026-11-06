import Mathlib

theorem algebra_19783 {x : ℕ} (hx : x > 0) (h1 : x ∣ 9) (h2 : x ∣ 12) (h3 : x ≠ 1) :
    x = 3 := by
  have h4 : x ≤ 9 := by
    exact Nat.le_of_dvd (by norm_num) h1
  interval_cases x <;> norm_num at h1 h2 h3 <;> all_goals tauto