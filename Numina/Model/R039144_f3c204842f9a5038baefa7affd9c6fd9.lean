import Mathlib

theorem algebra_191817 {a b c : ℝ} (ha : a ≥ b ∧ b ≥ c)
    (h1 : a^2 * b * c + a * b^2 * c + a * b * c^2 + 8 = a + b + c)
    (h2 : a^2 * b + a^2 * c + b^2 * c + b^2 * a + c^2 * a + c^2 * b + 3 * a * b * c = -4)
    (h3 : a^2 * b^2 * c + a * b^2 * c^2 + a^2 * b * c^2 = 2 + a * b + b * c + c * a)
    (h4 : a + b + c > 0) :
    round (a^5) = 1279 := by
  have h5 : a + b + c = 4 := by 
    nlinarith [sq_nonneg (a + b + c - 4), sq_nonneg (a * b + b * c + c * a + 1), sq_nonneg (a * b * c + 1)]

  have h6 : a * b + b * c + c * a = -1 := by
    nlinarith [h5, sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (c - 4)]

  have h7 : a * b * c = -1 := by
    nlinarith [h6, h3]

  have h7' : a ^ 3 -4*a^2 -a + 1 = 0 := by 
    nlinarith [ha.1, ha.2, h5, h6, h7, h1, h2, h3, sq_nonneg (a - 4), sq_nonneg (b - 1), sq_nonneg (c + 1)]

  have h17 : a ^ 5 >= (1278.5 : ℝ) := by
    nlinarith [sq_nonneg (a - 4.184), sq_nonneg (a^2 - 17.5)]

  have h18 : a ^ 5 <= (1279.5 : ℝ) := by
    nlinarith [sq_nonneg (a - 4.184), sq_nonneg (a^2 - 17.5)]

  rw [round_eq]
  simp only [Int.floor_eq_iff]
  constructor <;> (try linarith [h17, h18]) <;> (try nlinarith [sq_nonneg (a - 4), sq_nonneg (a^2 - 17.5), sq_nonneg (a^2 - 4.18^2 * a), sq_nonneg (a^2 - 17.5), sq_nonneg (b * c * a * 1), h1, h6, h7, h7'])

  all_goals linarith