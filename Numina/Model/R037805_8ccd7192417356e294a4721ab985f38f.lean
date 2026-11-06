import Mathlib

theorem algebra_325427 (x y : ℝ) : 5*x^2+10*y^2-12*x*y-6*x-4*y+13=0 ↔ (x=3 ∧ y=2) := by
  constructor
  · -- Assume 5*x^2+10*y^2-12*x*y-6*x-4*y+13=0 prove (x=3 ∧ y=2)
    intro h
    have h1 : (y - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (5 * (x - 3) - 6 * (y - 2)), sq_nonneg (2 * (x - 3) - 3 * (y - 2))]
    have hy : y = 2 := by
      nlinarith [h1]
    have hx : x = 3 := by
      rw [hy] at h
      have h2 : (x - 3) ^ 2 = 0 := by
        nlinarith
      nlinarith
    exact ⟨hx, hy⟩
  · -- Assume (x=3 ∧ y=2) prove 5*x^2+10*y^2-12*x*y-6*x-4*y+13=0
    rintro ⟨rfl, rfl⟩
    norm_num