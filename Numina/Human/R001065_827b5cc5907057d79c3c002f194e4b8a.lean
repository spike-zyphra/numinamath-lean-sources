import Mathlib

/- Positive integers $x$ and $y$ have a product of 56 and $x < y$. Seven times the reciprocal of the smaller integer plus 14 times the reciprocal of the larger integer equals 4. What is the value of $x$? -/
theorem algebra_20268 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (hxy : x * y = 56) (hxy1 : x < y) (h : 7 * (1/ x:ℚ) + 14 * (1/y:ℚ) = 4) :
    x = 2 := by
  -- xy=56, so y = 56/x
  have h1: y = 56/x := by
    rw [← hxy]
    symm
    apply Int.mul_ediv_cancel_left
    simp [hx.ne']
  have h1': (y:ℚ) = 56/x := by
    have: x*y = (56:ℚ) := by
      have: ↑(x*y) = (56:ℚ) := Int.cast_inj.mpr hxy
      rw [← this]; simp
    rw [← this]; field_simp
  -- substitute into 7/x + 14/y = 4, and we get an equation of x.
  have h2: (7/x:ℚ) + (x/4:ℚ) = 4 := by
    nth_rw 2 [← h]
    have hh1: 14 * (1/(56/x:ℚ)) = x/4 := by
      field_simp; ring
    rw [h1', hh1]
    ring
  -- therefore we get x^2-16x+28=0
  have h3: x^2-16*x+28 = 0 := by
    have hh1: (7/x:ℚ)+(x/4:ℚ)-4 = 0 := by
      rw [h2]; simp
    have hh2: (x^2-16*x+28:ℚ) = 4*(x*((7/x)+(x/4)-4)) := by
      field_simp; ring
    have hh3: (↑(x^2-16*x+28 : ℤ):ℚ) = (x^2-16*x+28:ℚ) := by
      simp
    rw [hh2, hh1, mul_zero, mul_zero] at hh3
    apply Int.cast_inj.mp hh3
  -- so (x-14)(x-2) = 0
  have h4: (x-14)*(x-2) = 0 := by
    rw [← h3]; ring
  -- x=14 or 2. but x < y, so x can only be 2.
  rcases (mul_eq_zero.mp h4) with x14 | x2
  · have hh1: x = 14 := by linarith [x14]
    rw [hh1] at hxy
    have hh2: y = 4 := by linarith [hxy]
    rw [hh1, hh2] at hxy1; norm_num at hxy1
  · linarith [x2]