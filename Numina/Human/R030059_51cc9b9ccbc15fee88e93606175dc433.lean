import Mathlib
/-let x,y,z be real numbers such that
x + y + z = 1 and x ^ 2 + y ^ 2 + z ^ 2 = 1
let m denote the minimum value of x ^ 3 + y ^ 3 + z ^ 3, find 9m-/
theorem algebra_102767 (x y z : ℝ) (h₀ : x + y + z = 1) (h₁ : x^2 + y^2 + z^2 = 1) :
    (x^3 + y^3 + z^3 ≥ 5 / 9) ∧ 
    (∃ x0 y0 z0: ℝ, (x0 + y0 + z0 = 1) ∧ (x0^2 + y0^2 + z0^2 = 1) ∧ (x0^3 + y0^3 + z0^3 = 5/9)) := by
  constructor

  -- prove the m is more than 5/9 -- 
  . have h2 : (x + y + z) ^ 2 = x^2 + y^2 + z^2 + 2 * (x * y + y * z + z * x) := by ring
    rw [h₀, h₁] at h2
    -- compute the value of x * y + y * z + z * x --
    have h3 : x * y + y * z + z * x = 0 := by linarith
    -- express x^3 + y^3 + z^3 in terms of x * y + y * z + z * x, x * y * z and x + y + z --
    have h4 : x^3 + y^3 + z^3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by ring
    rw [h4, h₀, h3]
    -- now we need to find lower bound of xyz --
    have h5 : x * y * z ≥ -4 / 27 := by
    -- we note that the "equality" may occur when x = y = z = 1/3 or x = 2/3, y = 2/3, z = -1/3, so we put them into nlinarith --
      nlinarith [sq_nonneg (x + y - 2 / 3), sq_nonneg (y + z - 2 / 3), sq_nonneg (z + x - 2 / 3),
        sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (z - 2 / 3),
        h₀, h₁, h3]

    linarith
  -- prove it's attainable --
  . use 2/3
    use 2/3
    use -1/3
    norm_num