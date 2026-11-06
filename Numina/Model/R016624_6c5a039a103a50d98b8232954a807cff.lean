import Mathlib

theorem algebra_121363 (x y : ℝ) :
    3*x^2+14*y^2-12*x*y+6*x-20*y+11=0 ↔ x=3 ∧ y=2 := by
  constructor
  · -- Assume 3*x^2+14*y^2-12*x*y+6*x-20*y+11=0 prove x=3 ∧ y=2
    intro h
    have h2 : 3 * x ^ 2 + 14 * y ^ 2 - 12 * x * y + 6 * x - 20 * y + 11 = 0 := h
    have h4 : (y - 2) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - 3 - 2 * (y - 2)), sq_nonneg (y - 2), sq_nonneg (3 * (x - 3) - 6 * (y - 2)), sq_nonneg ((x - 3) - (y - 2)), sq_nonneg ((x - 3) + (y - 2))]
    have hy : y = 2 := by 
      nlinarith [h4]
    have h5 : x - 3 = 0 := by
      rw [hy] at h2
      nlinarith
    have hx : x = 3 := by linarith 
    constructor <;> tauto 
  · -- Assume x=3 ∧ y=2 prove 3*x^2+14*y^2-12*x*y+6*x-20*y+11=0
    rintro ⟨hx, hy⟩ 
    rw [hx, hy]
    norm_num