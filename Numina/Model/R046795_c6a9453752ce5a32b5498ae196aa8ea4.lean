import Mathlib

theorem algebra_114931 (x y z : ℤ) :
    5*x^2+y^2+3*z^2-2*y*z=30 ↔
    (x=1 ∧ y=5 ∧ z=0) ∨ (x=1 ∧ y=-5 ∧ z=0) ∨ (x=-1 ∧ y=5 ∧ z=0) ∨ (x=-1 ∧ y=-5 ∧ z=0) := by 
  constructor 
  · -- Forward direction: equation implies the four possible solutions
    rintro h 
    have h1 : x ≤ 2 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (z - 0), sq_nonneg (y + 5), sq_nonneg (x^2), sq_nonneg ((y-z)^2), sq_nonneg (z^2), sq_nonneg ((y - 5)), sq_nonneg ((z - 0)), sq_nonneg ((y + 5)), sq_nonneg ((z - 0))]
    have h2 : x ≥ -2 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (z - 0), sq_nonneg (y + 5), sq_nonneg (x^2), sq_nonneg ((y-z)^2), sq_nonneg (z^2), sq_nonneg ((y - 5)), sq_nonneg ((z - 0)), sq_nonneg ((y + 5)), sq_nonneg ((z - 0))]
    have h3 : y ≤ 10 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (z - 0), sq_nonneg (y + 5), sq_nonneg (x^2), sq_nonneg ((y-z)^2), sq_nonneg (z^2), sq_nonneg ((y - 5)), sq_nonneg ((z - 0)), sq_nonneg ((y + 5)), sq_nonneg ((z - 0))]
    have h4 : y ≥ -10 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (z - 0), sq_nonneg (y + 5), sq_nonneg (x^2), sq_nonneg ((y-z)^2), sq_nonneg (z^2), sq_nonneg ((y - 5)), sq_nonneg ((z - 0)), sq_nonneg ((y + 5)), sq_nonneg ((z - 0))]
    have h5 : z ≤ 10 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (z - 0), sq_nonneg (y + 5), sq_nonneg (x^2), sq_nonneg ((y-z)^2), sq_nonneg (z^2), sq_nonneg ((y - 5)), sq_nonneg ((z - 0)), sq_nonneg ((y + 5)), sq_nonneg ((z - 0))]
    have h6 : z ≥ -10 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (z - 0), sq_nonneg (y + 5), sq_nonneg (x^2), sq_nonneg ((y-z)^2), sq_nonneg (z^2), sq_nonneg ((y - 5)), sq_nonneg ((z - 0)), sq_nonneg ((y + 5)), sq_nonneg ((z - 0))]
    interval_cases x <;> try { interval_cases y <;> try { interval_cases z <;> omega } }
    <;> omega
  · -- Backward direction: proving the four solutions satisfy the equation
    rintro (h | h | h | h)
    · -- First solution
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      all_goals norm_num 
    · -- Second solution
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      all_goals norm_num 
    · -- Third solution
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      all_goals norm_num 
    · -- Fourth solution
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      all_goals norm_num