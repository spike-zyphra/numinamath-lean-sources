import Mathlib

theorem algebra_5878 :
  IsGreatest {t : ℝ | ∃ x y, t = x^2 + 3*x - 2*y + y^2 ∧ |x + y| + |x - y| = 2016} 2037168 := by
  constructor
  · -- First part: show that 2037168 is in the set
    use 1008
    use -1008
    norm_num [abs_of_nonneg, abs_of_nonpos, abs_add]
  · -- Now prove maximum
    intro t
    rintro ⟨x, y, h_eq, h_abs⟩
    cases' abs_cases (x + y) with h1 h1
    · cases' abs_cases (x - y) with h2 h2
      · -- Case where $(x+y) \geq 0$ and $(x-y) \geq 0$.
        have hx : x = 1008 := by
          linarith
        rw [hx] at h_eq
        nlinarith [ sq_nonneg (y + 1008:ℝ), sq_nonneg ((y:ℝ) ), sq_nonneg ((1008:ℝ)), sq_nonneg ((-1008:ℝ)), sq_nonneg (2 * (y:ℝ) ) ]
      · -- Case where $(x+y) \geq 0$ and $(x-y) < 0$.
        have hy : y = 1008 := by
          linarith
        rw [hy] at h_eq
        nlinarith [ sq_nonneg (x - 1008:ℝ), sq_nonneg ((x:ℝ) ), sq_nonneg ((1008:ℝ)), sq_nonneg ((-1008:ℝ)), sq_nonneg (2 * (x:ℝ) ) ]
    · cases' abs_cases (x - y) with h2 h2
      · -- Case where $(x+y) < 0$ and $(x-y) \geq 0$.
        have hy : y = -1008 := by
          linarith
        rw [hy] at h_eq
        nlinarith [ sq_nonneg (x + 1008:ℝ), sq_nonneg ((x:ℝ) ), sq_nonneg ((-1008:ℝ)), sq_nonneg ((1008:ℝ)), sq_nonneg ((2 * (x:ℝ)) ) ]
      · -- Case where $(x+y) < 0$ and $(x - y) < 0$.
        have hx : x = -1008 := by
          linarith
        rw [hx] at h_eq
        nlinarith [ sq_nonneg ((y:ℝ) ), sq_nonneg ((-1008:ℝ)), sq_nonneg ((1008:ℝ)), sq_nonneg ((y + 1008:ℝ) ), sq_nonneg (2 * (y:ℝ) ) ]