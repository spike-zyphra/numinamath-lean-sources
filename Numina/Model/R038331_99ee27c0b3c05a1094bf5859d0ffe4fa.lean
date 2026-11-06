import Mathlib
open Real Set
open scoped BigOperators

theorem inequalities_122914 :
  IsLeast {
    t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ 
    x^2 + y^2 + z^2 = 1 ∧ t = x * y / z + y * z / x + z * x / y
  } (Real.sqrt 3) := by
  constructor
  · -- Show that sqrt(3) is in the set.
    use 1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3
    constructor
    · -- Show that 1 / sqrt 3 > 0
      have h1 : Real.sqrt 3 > 0 := by positivity
      positivity
    constructor
    · -- Show that 1 / sqrt 3 > 0
      have h1 : Real.sqrt 3 > 0 := by positivity
      positivity
    constructor
    · -- Show that 1 / sqrt 3 > 0
      have h1 : Real.sqrt 3 > 0 := by positivity
      positivity
    constructor
    · -- Show that x^2 + y^2 + z^2 = 1
      have h1 : Real.sqrt 3 > 0 := by positivity
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
    · -- Show that sqrt 3 = x * y / z + ...
      have h1 : Real.sqrt 3 > 0 := by positivity
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
  · -- Show sqrt(3) is the least element in the set.
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    -- We need to show real.sqrt 3 ≤ t
    have h2 : x * y / z + y * z / x + z * x / y ≥ Real.sqrt 3 := by
      have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
        have h4 : (x * y / z + y * z / x + z * x / y) ^ 2 =
            (x * y / z) ^ 2 + (y * z / x) ^ 2 + (z * x / y) ^ 2 + 2 * (x * y / z * (y * z / x) + x * y / z * (z * x / y) + y * z / x * (z * x / y)) := by 
          ring
        have h5 : x * y / z * (y * z / x) + x * y / z * (z * x / y) + y * z / x * (z * x / y) = x^2 + y^2 + z^2 := by 
          field_simp
          <;> nlinarith
        rw [h4, h5, h1]
        nlinarith [sq_nonneg ( (x * y / z) ^ 2 - (y * z / x) ^ 2 ), sq_nonneg ( (y * z / x) ^ 2 - (z * x / y) ^ 2 ), sq_nonneg ( (z * x / y) ^ 2 - (x * y / z) ^ 2 ), 
          sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y ), sq_nonneg (z * x / y - x * y / z ), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)
        ]
      have h6 : x * y / z + y * z / x + z * x / y ≥ 0 := by 
        positivity
      have h12 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ (Real.sqrt 3) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
      have h13 : (x * y / z + y * z / x + z * x / y) ≥ Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
      linarith
    linarith [ht, h2]