import Mathlib

theorem algebra_171210 (x y z : ℝ) (hx : |x| ≥ 2) (hy : |y| ≥ 2) (hz : |z| ≥ 2) :
    |x * y * z + 2 * (x + y + z)| ≥ 4 := by
  cases' abs_cases x with hx hx
  · -- x ≥ 0, so |x| ≥ 2 means x ≥ 2
    cases' abs_cases y with hy hy
    · -- y ≥ 0, so |y| ≥ 2 means y ≥ 2
      cases' abs_cases z with hz hz
      · -- z ≥ 0, so |z| ≥ 2 means z ≥ 2
        have h1 : x * y * z + 2 * (x + y + z) ≥ 20 := by
          nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ y - 2 by linarith),
                mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (show 0 ≤ y - 2 by linarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ y - 2 by linarith)) (show 0 ≤ z - 2 by linarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonneg (by linarith)]
          nlinarith
        linarith
      · -- z < 0, so |z| ≥ 2 means z ≤ -2
        have h1 : x * y * z + 2 * (x + y + z) ≤ -4 := by
          nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ y - 2 by linarith),
                mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (show 0 ≤ y - 2 by linarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ y - 2 by linarith)) (show 0 ≤ -z - 2 by nlinarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonpos (by linarith)]
          nlinarith
        linarith
    · -- y < 0, so |y| ≥ 2 means y ≤ -2
      cases' abs_cases z with hz hz
      · -- z ≥ 0, so |z| ≥ 2 means z ≥ 2
        have h1 : x * y * z + 2 * (x + y + z) ≤ -4 := by
          nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ -y - 2 by nlinarith),
                mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (show 0 ≤ -y - 2 by nlinarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ -y - 2 by nlinarith)) (show 0 ≤ z - 2 by linarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonpos (by linarith)]
          nlinarith
        linarith
      · -- z < 0, so |z| ≥ 2 means z ≤ -2
        have h1 : x * y * z + 2 * (x + y + z) ≥ 4 := by
          nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ -y - 2 by nlinarith),
                mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (show 0 ≤ -y - 2 by nlinarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ -y - 2 by nlinarith)) (show 0 ≤ -z - 2 by nlinarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonneg (by linarith)]
          nlinarith
        linarith
  · -- x < 0, so |x| ≥ 2 means x ≤ -2
    cases' abs_cases y with hy hy
    · -- y ≥ 0, so |y| ≥ 2 means y ≥ 2
      cases' abs_cases z with hz hz
      · -- z ≥ 0, so |z| ≥ 2 means z ≥ 2
        have h1 : x * y * z + 2 * (x + y + z) ≤ -4 := by
          nlinarith [mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ y - 2 by linarith),
                mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (show 0 ≤ y - 2 by linarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ y - 2 by linarith)) (show 0 ≤ z - 2 by linarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonpos (by linarith)]
          nlinarith
        linarith
      · -- z < 0, so |z| ≥ 2 means z ≤ -2
        have h1 : x * y * z + 2 * (x + y + z) ≥ 4 := by
          nlinarith [mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ y - 2 by linarith),
                mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (show 0 ≤ y - 2 by linarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ y - 2 by linarith)) (show 0 ≤ -z - 2 by nlinarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonneg (by linarith)]
          nlinarith
        linarith
    · -- y < 0, so |y| ≥ 2 means y ≤ -2
      cases' abs_cases z with hz hz
      · -- z ≥ 0, so |z| ≥ 2 means z ≥ 2
        have h1 : x * y * z + 2 * (x + y + z) ≥ 4 := by
          nlinarith [mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ -y - 2 by nlinarith),
                mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (show 0 ≤ -y - 2 by nlinarith) (show 0 ≤ z - 2 by linarith),
                mul_nonneg (mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ -y - 2 by nlinarith)) (show 0 ≤ z - 2 by linarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonneg (by linarith)]
          nlinarith
        linarith
      · -- z < 0, so |z| ≥ 2 means z ≤ -2
        have h1 : x * y * z + 2 * (x + y + z) ≤ -4 := by
          nlinarith [mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ -y - 2 by nlinarith),
                mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (show 0 ≤ -y - 2 by nlinarith) (show 0 ≤ -z - 2 by nlinarith),
                mul_nonneg (mul_nonneg (show 0 ≤ -x - 2 by nlinarith) (show 0 ≤ -y - 2 by nlinarith)) (show 0 ≤ -z - 2 by nlinarith)]
        have h2 : |x * y * z + 2 * (x + y + z)| ≥ 4 := by
          rw [abs_of_nonpos (by linarith)]
          nlinarith
        linarith