import Mathlib
open Real

/- Two right circular cylinders have the same volume. The radius of the second
cylinder is 10% more than the radius of the first. What is the relationship between
the heights of the two cylinders?
(A) The second height is 10% less than the first.
(B) The first height is 10% more than the second.
(C) The second height is 21% less than the first.
(D) The first height is 21% more than the second.
(E) The second height is 80% of the first. -/
theorem algebra_95315 {r1 r2 h1 h2 : ℝ} (hr1 : r1 > 0) (hr2 : r2 > 0)
(hvol : π * r1^2 * h1 = π * r2^2 * h2) (hrr : r2 = 1.1 * r1) :
h1 = 121 / 100 * h2 := by
  -- adjust the positions of the terms and then eliminate them
  rw [pow_two,
      pow_two,
      hrr,
      mul_assoc,
      mul_assoc,
      mul_assoc,
      mul_assoc,
      mul_comm 1.1 _,
      mul_assoc,
      mul_assoc,
      ← mul_assoc 1.1 _,
      mul_comm 1.1 _,
      mul_assoc,
      ] at hvol
  simp [Real.pi_pos,Real.pi_ne_zero,hr1,((by linarith):r1≠0)] at hvol
  rw [← mul_assoc] at hvol
  rw [((by ring):121 / 100 = (1.1:ℝ) * 1.1)]
  exact hvol