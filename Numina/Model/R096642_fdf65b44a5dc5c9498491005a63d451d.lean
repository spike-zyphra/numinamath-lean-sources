import Mathlib

theorem algebra_267198 (x : ℝ) (hx : x > 0) (hvol : (3^3 + 12^3 + x^3) / 3 = 700) :
    round x = 7 := by
  have h1 : 3^3 + 12^3 + x^3 = 2100 := by
    linarith
  have h2 : x^3 = 345 := by
    nlinarith
  have h4 : x > (7 : ℝ) := by
    by_contra h
    nlinarith [sq_nonneg (x - 7 : ℝ), sq_nonneg (x + 7 : ℝ), sq_nonneg (x^2 + 7^2 + x * 7 : ℝ)]
  have h5 : x < (7.5 : ℝ) := by
    by_contra h
    nlinarith [sq_nonneg (x - 7.5 : ℝ), sq_nonneg (x + 7.5 : ℝ), sq_nonneg (x^2 + 7.5^2 + x * 7.5 : ℝ)]
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor <;> (try linarith)
  all_goals
    nlinarith