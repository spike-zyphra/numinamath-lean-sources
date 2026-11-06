import Mathlib

-- Two Coinciding Triples. None of the three positive numbers x, y, z is less than the minimum of the three positive numbers a, b, c. None of the numbers x, y, z is greater than the maximum of the numbers a, b, c. It is also known that x + y + z = a + b + c and xyz = abc. Show that the set {x, y, z} coincides with the set {a, b, c}.
theorem algebra_270786 (x y z a b c : ℝ)
    (hle1 : 0 < x ∧ x ≤ y ∧ y ≤ z)
    (hle2 : 0 < a ∧ a ≤ b ∧ b ≤ c)
    (hle3 : a ≤ x)
    (hle4 : z ≤ c)
    (heq1 : x+y+z = a+b+c)
    (heq2: x*y*z = a*b*c) : x = a ∧ y = b ∧ z = c := by

  -- Key idea: Use the symmetry of the expressions and the sum and product constraints.
  -- First, expand the symmetric polynomials and relate them using the given equalities.

  -- Step 1: Construct a symmetric expression involving the variables and parameters.
  -- The following formula relates the difference in the second symmetric polynomial:
  have h1 : a*b*c*(a*b+b*c+c*a-x*y-y*z-z*x) = b*c*(x-a)*(y-a)*(z-a) := by
    -- Expand (x-a)(y-a)(z-a) and express it in terms of symmetric sums and products.
    have : b*c*(x-a)*(y-a)*(z-a) = b*c*(x*y*z-a*(x*y+y*z+z*x)+a*a*(x+y+z)-a*a*a) := by ring
    -- Substitute the given sum and product equalities.
    rw [heq1, heq2] at this
    rw [this]
    ring

  -- Similarly, a symmetric expression with respect to c.
  have h2 : a*b*c*(a*b+b*c+c*a-x*y-y*z-z*x) = a*b*(x-c)*(y-c)*(z-c) := by
    have : a*b*(x-c)*(y-c)*(z-c) = a*b*(x*y*z-c*(x*y+y*z+z*x)+c*c*(x+y+z)-c*c*c) := by ring
    rw [heq1, heq2] at this
    rw [this]
    ring

  -- Step 2: Use the order constraints to deduce sign information.
  -- Since x, y, z are all ≥ a, their differences with a are nonnegative.
  have : a*b*c*(a*b+b*c+c*a-x*y-y*z-z*x) ≥ 0 := by
    rw [h1]
    have : x - a ≥ 0 := by linarith
    have : y - a ≥ 0 := by linarith
    have : z - a ≥ 0 := by linarith
    -- The product of nonnegative terms is nonnegative.
    apply Left.mul_nonneg ?h1 (by linarith)
    apply Left.mul_nonneg ?h2 (by linarith)
    apply Left.mul_nonneg ?h3 (by linarith)
    nlinarith

  -- Similarly, since z ≤ c, x, y, z ≤ c, so their differences with c are nonpositive.
  have : a*b*c*(a*b+b*c+c*a-x*y-y*z-z*x) ≤ 0 := by
    rw [h2]
    -- The product of nonpositive terms is nonpositive.
    apply mul_nonpos_of_nonneg_of_nonpos ?hh1 (by linarith)
    apply mul_nonneg_of_nonpos_of_nonpos ?hh2 (by linarith)
    apply mul_nonpos_of_nonneg_of_nonpos ?hh3 (by linarith)
    nlinarith

  -- Step 3: Combine the two inequalities to deduce equality.
  have : a*b*c*(a*b+b*c+c*a-x*y-y*z-z*x) = 0 := by linarith
  rw [this] at h1
  rw [this] at h2

  -- Step 4: Use contradiction to show x = a.
  have hx : x = a := by
    by_contra hx
    -- If x ≠ a, then x > a by the order assumption.
    have : x > a := by exact lt_of_le_of_ne hle3 fun a_1 => hx (id (Eq.symm a_1))
    -- Then the product (x-a)(y-a)(z-a) is strictly positive.
    have : b * c * (x - a) * (y - a) * (z - a) > 0 := by
      apply mul_pos ?hhh1 (by linarith)
      apply mul_pos ?hhh2 (by linarith)
      apply mul_pos ?hhh3 (by linarith)
      nlinarith
    -- This contradicts the previous equality.
    linarith

  -- Step 5: Similarly, show z = c.
  have hz : z = c := by
    by_contra hz
    -- If z ≠ c, then z < c by the order assumption.
    have : z < c := by exact lt_of_le_of_ne hle4 hz
    -- Then the product (x-c)(y-c)(z-c) is strictly negative.
    have : a * b * (x - c) * (y - c) * (z - c) < 0 := by
      apply mul_neg_of_pos_of_neg ?hhhh1 (by linarith)
      apply mul_pos_of_neg_of_neg ?hhhh2 (by linarith)
      apply mul_neg_of_pos_of_neg ?hhhh3 (by linarith)
      nlinarith
    -- This also contradicts the previous equality.
    linarith

  -- Step 6: Now x = a and z = c, use the sum constraint to deduce y = b.
  constructor
  · exact hx
  · constructor
    · rw [hx, hz] at heq1
      simp at heq1
      exact heq1
    · exact hz
