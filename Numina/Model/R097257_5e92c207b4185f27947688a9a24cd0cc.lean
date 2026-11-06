import Mathlib

theorem algebra_9447_1 (x y z : ℝ) (h0 : x + y + z = 0) (h1 : (x - y)^2 + (y - z)^2 + (z - x)^2 ≤ 2) :
    x ≤ 2 / 3 ∧ x ≥ -2 / 3 := by
  -- Note on formulation of the problem:
  -- algebra_9447_1 proves that for any x, y, z satisfying x + y + z = 0 and (x - y)^2 + (y - z)^2 + (z - x)^2 ≤ 2, -2/3 ≤ x ≤ 2/3
  -- algebra_9447_2 proves that there exists x, y, z satisfying x + y + z = 0 and (x - y)^2 + (y - z)^2 + (z - x)^2 = 2, x = 2/3
  -- algebra_9447_3 proves that there exists x, y, z satisfying x + y + z = 0 and (x - y)^2 + (y - z)^2 + (z - x)^2 = 2, x = -2/3
  -- Thus the maximum and minimum values of x are 2/3 and -2/3 respectively

  -- x = -y - z
  replace h0 : x = -y - z := by linarith
  -- The hypothesis simplifies to 2x^2 + y^2 + z^2 - yz ≤ 1
  replace h1 : x^2 + y^2 + z^2 - x*y - y*z - z*x ≤ 1 := by linarith
  replace h1 : 2*x^2 + y^2 + z^2 - y*z ≤ 1 := by
    have h2 : x^2 + y^2 + z^2 - x*y - y*z - z*x = 2*x^2 + y^2 + z^2 - y*z := by
      rw [h0]
      ring
    rwa [h2] at h1

  -- y^2 + z^2 - yz = ((y + z)^2 + 3 * (y - z)^2) / 4 ≥ (y + z)^2 / 4 = x^2 / 4
  have h2 : y^2 + z^2 - y*z ≥ x^2 / 4 := by
    calc y^2 + z^2 - y*z = ((y + z)^2 + 3 * (y - z)^2) / 4 := by ring
                       _ ≥ (y + z)^2 / 4 := by linarith [sq_nonneg (y - z)]
                       _ = x^2 / 4 := by rw [h0]; ring

  -- We get x^2 ≤ 4/9 and problem solved
  constructor <;> nlinarith

theorem algebra_9447_2 : ∃ x y z : ℝ, x + y + z = 0 ∧ (x - y)^2 + (y - z)^2 + (z - x)^2 = 2 ∧ x = 2 / 3 := by
  -- Use x = 2/3, y = z = -1/3
  use 2 / 3, -1 / 3, -1 / 3
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem algebra_9447_3 : ∃ x y z : ℝ, x + y + z = 0 ∧ (x - y)^2 + (y - z)^2 + (z - x)^2 = 2 ∧ x = -2 / 3 := by
  -- Use x = -2/3, y = z = 1/3
  use -2 / 3, 1 / 3, 1 / 3
  refine ⟨?_, ?_, ?_⟩ <;> norm_num