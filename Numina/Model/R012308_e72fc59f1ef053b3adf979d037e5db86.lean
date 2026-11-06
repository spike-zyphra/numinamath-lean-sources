import Mathlib

theorem algebra_18723 {x y : ℕ} (hxy : x * y = 1000) (hx : ¬10 ∣ x) (hy : ¬10 ∣ y) :
x + y = 133 := by
  have h1 : x ∣ 1000 := by
    use y
    all_goals nlinarith
  have h2 : y ∣ 1000 := by
    use x
    all_goals nlinarith
  have h3 : x ≤ 1000 := by
    exact Nat.le_of_dvd (by norm_num) h1
  have h4 : y ≤ 1000 := by
    exact Nat.le_of_dvd (by norm_num) h2
  interval_cases x <;> omega