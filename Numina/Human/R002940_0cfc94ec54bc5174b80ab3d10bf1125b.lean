import Mathlib
/- 37th IMO 1996 shortlist Problem 1 x, y, z are positive real numbers with product 1. Show that xy/(x 5 + xy + y 5 ) + yz/(y 5 + yz + z 5 ) + zx/(z 5 + zx + x 5 ) ≤ 1. When does equality occur? Solution -/
theorem inequalities_602032 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 1) :
x * y / (x ^ 5 + x * y + y ^ 5) + y * z / (y ^ 5 + y * z + z ^ 5) + z * x / (z ^ 5 + z * x + x ^ 5) ≤ 1 ∧
(x * y / (x ^ 5 + x * y + y ^ 5) + y * z / (y ^ 5 + y * z + z ^ 5) + z * x / (z ^ 5 + z * x + x ^ 5) = 1 ↔
(x = 1 ∧ y = 1 ∧ z = 1)):= by
  -- Key inequality: For positive x and y, we have x^5 + x*y + y^5 ≥ x^2*y^2*(x+y) + x*y
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x ^ 5 + x * y + y ^ 5 ≥ x ^ 2 * y ^ 2 * (x + y) + x * y:= by
    intro x y hx hy
    -- This is proven by showing that (x+y)*(x^2+x*y+y^2)*(x-y)^2 ≥ 0
    have h1 : (x + y) * (x ^ 2 + x * y + y ^ 2) * (x - y) ^ 2 ≥ 0:= by positivity
    linarith

  -- Apply the key inequality to different pairs of variables
  have h2:= h1 z x hz hx
  have h3:= h1 x y hx hy
  replace h1:= h1 y z hy hz

  -- Establish that products of variables are non-negative
  have g1 : y * z ≥ 0:= by positivity
  have g2 : z * x ≥ 0:= by positivity
  have g3 : x * y ≥ 0:= by positivity

  -- Establish that denominators in the simplified expression are positive
  have g5 : z ^ 2 * x ^ 2 * (z + x) + z * x ≥ 0:= by positivity
  have g4 : y ^ 2 * z ^ 2 * (y + z) + y * z ≥ 0:= by positivity
  have g6 : x ^ 2 * y ^ 2 * (x + y) + x * y ≥ 0:= by positivity

  -- Apply division inequality to each term
  replace h1:= div_le_div_of_nonneg_left g1 (by positivity) h1
  replace h2:= div_le_div_of_nonneg_left g2 (by positivity) h2
  replace h3:= div_le_div_of_nonneg_left g3 (by positivity) h3

  -- Key step: Show that the sum of the simplified fractions equals 1
  have h4 : y * z / (y ^ 2 * z ^ 2 * (y + z) + y * z) + z * x / (z ^ 2 * x ^ 2 * (z + x) + z * x) + x * y / (x ^ 2 * y ^ 2 * (x + y) + x * y) = 1:= by
    rw [show x * y = (x * y * z) * (x * y) by rw [hxyz] ; simp]
    rw [show y * z = (x * y * z) * (y * z) by rw [hxyz] ; simp]
    rw [show z * x = (x * y * z) * (z * x) by rw [hxyz] ; simp]
    field_simp
    ring_nf

  -- Construct the conjunction for the theorem statement
  constructor
  -- First part: Prove the inequality
  .
    linarith

  -- Second part: Characterize when equality holds
  .
    constructor
    -- Forward direction: If equality holds, then x = y = z = 1
    .
      intro h5
      replace h1 : y * z / (y ^ 5 + y * z + z ^ 5) = y * z / (y ^ 2 * z ^ 2 * (y + z) + y * z):= by linarith
      replace h2 : z * x / (z ^ 5 + z * x + x ^ 5) = z * x / (z ^ 2 * x ^ 2 * (z + x) + z * x):= by linarith
      clear g1 g2 g3 g4 g5 g6 h4 h5
      field_simp at h1 h2

      -- Show that y = z and z = x by analyzing when the inequalities become equalities
      replace h1 : (y + z) * (y ^ 2 + y * z + z ^ 2) * (y - z) ^ 2 = 0:= by linarith
      replace h2 : (z + x) * (z ^ 2 + z * x + x ^ 2) * (z - x) ^ 2 = 0:= by linarith
      have g1 : (y + z) * (y ^ 2 + y * z + z ^ 2) ≠ 0:= by positivity
      have g2 : (z + x) * (z ^ 2 + z * x + x ^ 2) ≠ 0:= by positivity
      simp [g1] at h1
      simp [g2] at h2
      replace h1 : y = z:= by linarith
      replace h2 : z = x:= by linarith
      subst y z

      -- With x = y = z, use the constraint x*y*z = 1 to show x = 1
      replace habc : (x - 1) * ((2 * x + 1) ^ 2 + 3) = 0:= by linarith
      have g3 : (2 * x + 1) ^ 2 + 3 ≠ 0:= by positivity
      simp [g3] at habc
      simp
      linarith

    -- Reverse direction: If x = y = z = 1, then equality holds
    .
      rintro ⟨rfl, rfl, rfl⟩
      norm_num
