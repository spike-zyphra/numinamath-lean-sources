import Mathlib
/-
The train schedule in Hummut is hopelessly unreliable. Train A will enter Intersection X from the west at a random time between 9:00 am and 2:30 pm; each moment in that interval is equally likely. Train B will enter the same intersection from the north at a random time between 9:30 am and 12:30 pm, independent of Train A; again, each moment in the interval is equally likely. If each train takes 45 minutes to clear the intersection, what is the probability of a collision today?
-/

-- Time interval for Train A is 330 minutes.
def L_A : ℚ := 330
-- Time interval for Train B is 180 minutes.
def L_B : ℚ := 180

-- Total area of the sample space in the time-time plane.
def A_total : ℚ := L_A * L_B

-- Region 1 (S₁) is a triangle
def A₁ : ℚ := (1 / 2) * 165 * 165

-- Region 2 (S₂) is a trapezoid
def A₂ : ℚ := (1 / 2) * (255 + 75) * 180

-- The area of the collision region is the total area minus the non-collision areas.
def A_coll : ℚ := A_total - (A₁ + A₂)

-- The probability of a collision is the ratio of the collision area to the total area.
def P_coll : ℚ := A_coll / A_total

theorem combinatorics_611426 : P_coll = 13 / 48 := by
  unfold P_coll A_coll A_total A₁ A₂ L_A L_B
  norm_num

