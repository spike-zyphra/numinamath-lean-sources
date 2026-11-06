import Mathlib

theorem algebra_250851 (a : ℕ → ℚ) (ha : a 0 = 1 / 2) (ha' : a 1 = 5 / 8)
    (ha'' : a 2 = 3 / 4) (ha''' : a 3 = 7 / 8) (ha'''' : a 4 = 1) (ha''''' : a 5 = 9 / 8)
    (ha'''''' : a 6 = 5 / 4) :
    a 4 = 1 ∧ a 5 = 9 / 8 ∧ a 6 = 5 / 4 := by
  exact ⟨ha'''', ha''''', ha''''''⟩