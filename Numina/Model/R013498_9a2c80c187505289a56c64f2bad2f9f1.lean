import Mathlib

theorem algebra_6166
  (x y z : ℝ)
  (hxpos : 0 < x)
  (hypos : 0 < y)
  (hzpos : 0 < z)
  (h1 : x + 1 / y = 4)
  (h2 : y + 1 / z = 1)
  (h3 : z + 1 / x = 7 / 3) :
  x * y * z = 1 := by
  have eq1 : x * y + 1 = 4 * y := by
    have hyne0 : y ≠ 0 := by linarith
    field_simp at h1 ⊢
    nlinarith
  have eq2 : y * z + 1 = z := by
    have hzne0 : z ≠ 0 := by linarith
    field_simp at h2 ⊢
    nlinarith
  have eq3 : 3 * x * z + 3 = 7 * x := by 
    have hxne0 : x ≠ 0 := by linarith
    field_simp at h3 ⊢
    nlinarith
  -- From eq2: $y * z + 1 = z$, we get $y = \frac{z - 1}{z}$.
  have eq5 : y = (z - 1) / z := by
    have hzne0 : z ≠ 0 := by linarith
    field_simp at eq2 ⊢
    nlinarith 
  -- From eq2, we can also get $z = \frac{1}{1 - y}$.
  have hzne1 : z - 1 ≠ 0 := by
    by_contra h
    have hz1 : z = 1 := by linarith
    rw [hz1] at eq2
    have hy0 : y = 0 := by 
      nlinarith
    nlinarith
  -- From eq1: $x * y + 1 = 4 * y$, we get $x = \frac{4 * y - 1}{y}$.
  have eq4 : x = (4 * y - 1) / y := by
    have hyne0 : y ≠ 0 := by linarith
    field_simp at eq1 ⊢
    nlinarith 
  -- Use eq4 and eq1 to solve for x in terms of z and substituting y.
  have eq7 : x = -3 / (3 * z - 7) := by
    have hzne7 : 3 * z - 7 ≠ 0 := by
      by_contra h
      have h1 : 3 * z - 7 = 0 := by linarith
      have hz7 : z = 7 / 3 := by linarith
      rw [hz7] at eq2 eq3
      nlinarith [sq_pos_of_pos hxpos, sq_pos_of_pos hypos, sq_pos_of_pos hzpos]
    have hxne0 : x ≠ 0 := by linarith
    field_simp at eq3 ⊢
    nlinarith
  -- From eq5 and eq4 we have x in the two different expressions,they equal.
  have eq6 : x = (3 * z - 4) / (z - 1) := by
    rw [eq5] at eq4
    have hzne0 : z ≠ 0 := by linarith
    have hzne1 : z - 1 ≠ 0 := by
      by_contra h
      have hz1 : z = 1 := by linarith
      rw [hz1] at eq2
      have hy0 : y = 0 := by 
        nlinarith
      nlinarith
    field_simp at eq4 ⊢
    <;> nlinarith
  -- Now equating eq7 and eq6 to get the quadratic.
  have heq8 : (3 * z - 4) / (z - 1) = -3 / (3 * z - 7) := by
    nlinarith [eq6, eq7]
  -- Solving quadratic $9z^2 - 30z + 25=0$ now.
  have hzquadratic : 9 * z ^ 2 - 30 * z + 25 = 0 := by 
    have hzne1 : z - 1 ≠ 0 := by
      by_contra h
      have hz1 : z = 1 := by linarith
      rw [hz1] at eq2
      have hy0 : y = 0 := by
        nlinarith
      nlinarith
    have hzne7 : 3 * z - 7 ≠ 0 := by
      by_contra h
      have h1 : 3 * z - 7 = 0 := by linarith
      have hz7 : z = 7 / 3 := by linarith
      rw [hz7] at eq2 eq3
      nlinarith [sq_pos_of_pos hxpos, sq_pos_of_pos hypos, sq_pos_of_pos hzpos]
    field_simp [hzne1, hzne7] at heq8 ⊢
    <;> nlinarith [heq8]
  -- Solving quadratic to get the exact value of z.
  have hz5 : z = 5 / 3 := by
    nlinarith [hzquadratic, hzpos]
  -- Substituting back to get the value y and x.
  have hy25 : y = 2 / 5 := by
    rw [hz5] at eq5 
    field_simp at eq5 ⊢
    nlinarith
  -- Solving the value of x.
  have hx32 : x = 3 / 2 := by 
    rw [hy25] at eq4
    field_simp at eq4 ⊢
    nlinarith 
  -- Finally proving the product is 1.
  rw [hx32, hy25, hz5]
  norm_num