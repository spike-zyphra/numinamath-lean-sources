import Mathlib
open Polynomial

/-A car travels due east at 2/3 mile per minute on a long, straight road.
At the same time, a circular storm, whose radius is 51 miles,
moves southeast at 1/2 * sqrt(2) mile per minute. At time t=0,
the center of the storm is 110 miles due north of the car.
At time t=t_1 minutes, the car enters the storm circle, and at time
t=t_2 minutes, the car leaves the storm circle. Find 1/2 * (t_1 + t_2).-/


-- We make a few assumptions about the problem:
-- 1. t1, t2 are positive real numbers.
-- 2. The car's coordinates are given by (2/3 * t, 0).
-- 3. The storm's coordinates are given by (1/2 * t, 110 - 1/2 * t).
-- These are calculated using the given speeds and the initial position of the storm and the car.
-- 4. The equation of the circle is given by the distance formula, which is set equal to the radius squared (51^2).
-- Here we assume that the storm as center with center's coordinates (1/2 * t, 110 - 1/2 * t) and radius 51 miles.
-- 5. The quadratic equation is derived from the circle equation, and we can find the roots of this polynomial to get t1 and t2.
-- This is because the car enters and leaves the storm circle at these times. Mathematically these are the roots of the quadratic
-- equation we form using the equation of the circle.
-- 6. The sum of the roots of a quadratic equation ax^2 + bx + c = 0 is given by -b/a. In our case, we can find the sum of the roots and divide by 2,
-- which is our goal.

theorem algebra_96843
(t1 t2 t: ℝ)
(ht1 : t1 > 0)
(ht2 : t2 > 0)
(carCoord stormCoord: ℝ × ℝ)

(h_carCoord: carCoord = (2/3 * t, 0))
(h_stormCoord: stormCoord = (1/2 * t, 110 - 1/2 * t))
(h_sumQuadratic: (5/18 * t^2 - 110 * t + 9499 = 0) → (t1 + t2) = - (-110/(5/18)))
(h_circleEqn: (carCoord.1 - stormCoord.1)^2 + (carCoord.2 - stormCoord.2)^2 - 51^2 = 0):
(t1 + t2)/ 2 = 198 := by 
  have eqn1 : (2/3 * t - 1/2 * t)^2 + (0 - (110 - 1/2 * t))^2 - 51^2 = 0 := by 
    simp [h_carCoord, h_stormCoord] at h_circleEqn ⊢
    linarith
  ring_nf at eqn1 
  have h_quadratic : 5/18 * t^2 - 110 * t + 9499 = 0 := by 
    nlinarith 
  have h_sum1 : (t1 + t2) = - (-110/(5/18)) := by 
    apply h_sumQuadratic 
    linarith 
  have h_sum2 : (t1 + t2)/ 2 = 198 := by 
    rw [show t1 + t2 = - (-110 / (5/18 : ℝ)) by linarith [h_sum1]]
    field_simp 
    <;> linarith 
  exact h_sum2