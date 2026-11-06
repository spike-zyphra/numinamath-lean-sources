import Mathlib

theorem algebra_5772 :
  IsLeast {x^2 - 8 * x + 18 | x : ℝ} 2 := by
  constructor
  · -- Show 2 belongs to the set
    use 4
    norm_num
  · -- Show no value less than 2 belongs to the set
    intro y
    rintro ⟨x, hx⟩
    have h1 : x^2 - 8 * x + 18 ≥ 2 := by
      have h2 : x^2 - 8 * x + 18 = (x - 4) ^ 2 + 2 := by
        ring
      rw [h2]
      have h3 : (x - 4) ^ 2 ≥ 0 := by
        exact sq_nonneg (x - 4)
      linarith
    linarith