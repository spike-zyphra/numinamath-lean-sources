import Mathlib

theorem algebra_189485 (x y : ℕ) (hx : 10 ≤ x) (hy : 10 ≤ y)
    (hxy : x < 20 ∧ y < 20) :
    (x + (y % 10)) * 10 + (x % 10) * (y % 10) = x * y := by 
  rcases hxy with ⟨hx2, hy2⟩
  interval_cases x <;> interval_cases y 
    <;> norm_num
  all_goals omega