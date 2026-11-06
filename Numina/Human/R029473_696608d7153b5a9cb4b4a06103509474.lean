import Mathlib

/--
Example 7 Let $x=2 \frac{1}{5}, y=-\frac{5}{11}, z=-2 \frac{1}{5}$. Then $x^{2}+x z+2 y z+3 x+3 z+4 x y+5=$
-/
theorem algebra_321795 (x y z : ℝ) (hx : x = 2 + 1 / 5) (hy : y = -5 / 11) (hz : z = -(2 + 1 / 5)) :
  x ^ 2 + x * z+ 2 * y * z + 3 * x + 3 * z + 4 * x * y + 5 = 3 := by
  --  x = 11/5, y = -5/11, z = -11/5.
  have h1 : x = 11 / 5 ∧ y = -5 / 11 ∧ z = -11 / 5 := by
    simp [hx, hy, hz]
    norm_num
  -- First term: x² = 121/25.
  have h2 : x ^ 2 = 121 / 25 := by
    rw [h1.left]
    norm_num
  -- Second term: xz. Multiply x and z. x is 11/5, z is -11/5. Multiplying them: (11/5)*(-11/5) = -121/25.
  have h3 : x * z = -121 / 25 := by
    rw [h1.left, h1.right.right]
    norm_num
  -- Third term: 2yz. Compute y*z first, then multiply by 2. y is -5/11, z is -11/5. Multiplying y and z: (-5/11)*(-11/5) = 1. Then multiply by 2: 2*1 = 2.
  have h4 : 2 * y * z = 2 := by
    rw [h1.right.left, h1.right.right]
    norm_num
  -- Fourth term: 3x. 3 times 11/5 is (3*11)/5 = 33/5.
  have h5 : 3 * x = 33 / 5 := by
    rw [h1.left]
    norm_num
  -- Fifth term: 3z. 3 times (-11/5) is -33/5.
  have h6 : 3 * z = -33 / 5 := by
    rw [h1.right.right]
    norm_num
  -- Sixth term: 4xy. Multiply x and y first, then multiply by 4. x is 11/5, y is -5/11. Multiplying x and y: (11/5)*(-5/11) = -1. Multiply by 4: 4*(-1) = -4.
  have h7 : 4 * x * y = -4 := by
    rw [h1.left, h1.right.left]
    norm_num
  -- Now combining: 121/25 - 121/25 + 2 + 33/5 - 33/5 - 4 + 5 = 3.
  simp [h2, h3, h4, h5, h6, h7]
  norm_num