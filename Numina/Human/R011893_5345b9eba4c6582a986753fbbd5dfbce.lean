import Mathlib

/-Given real numbers x y z u satisfy
x / (y + z + u)
= y / (z + u + x)
= z / (u + x + y)
= u / (x + y + z)
Find the value of
 (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) -/

theorem algebra_300027 {x y z u: ℝ} (ne1: y + z + u ≠ 0) (ne2: z + u + x ≠ 0) (ne3: u + x + y ≠ 0) (ne4: x + y + z ≠ 0) 
  (ne5: z + u ≠ 0) (ne6: u + x ≠ 0) (ne7: x + y ≠ 0) (ne8: y + z ≠ 0)
   (h1: x / (y + z + u) = y / (z + u + x)) (h2: y / (z + u + x) = z / (u + x + y)) 
    (h3: z / (u + x + y) = u / (x + y + z)): 
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = -4 ∨ 
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = 4 := by

    set k:= x / (y + z + u)
    have hx:  x / (y + z + u) = k := by linarith
    have hy: y / (z + u + x) = k := by linarith
    have hz: z / (u + x + y) = k := by linarith
    have hu: u / (x + y + z) = k := by linarith
    clear h1 h2 h3
    replace hx: x = k * (y + z + u) := by
      field_simp [ne1] at hx
      linarith
    replace hy: y = k * (z + u + x) := by
      field_simp [ne2] at hy
      linarith
    replace hz: z = k * (u + x + y) := by
      field_simp [ne3] at hz
      linarith
    replace hu: u = k * (x + y + z) := by
      field_simp [ne4] at hu
      linarith
    have o: x + y + z + u = 3 * k * (x + y + z + u) := by
      nlinarith
    replace o: (3 * k - 1) * (x + y + z + u) = 0 := by
        linarith
    simp at o
    rcases o with o | o
    -- 3k - 1 = 0
    .
      replace o: k = 1 / 3 := by linarith
      simp [o] at *
      have gy: y = x := by nlinarith
      have gz: z = x := by nlinarith
      have gu: u = x := by nlinarith
      have t: x ≠ 0 := by
        by_contra! t
        simp [t] at gy gz gu
        simp [gy, gz, gu] at ne1
      replace t: x + x ≠ 0 := by
        by_contra! s
        simp at s
        simp [s] at t
      simp [gy, gz, gu]
      right
      field_simp
      norm_num
    -- 3k - 1 ≠ 0
    .
      have r1: (x + y) / (z + u) = -1 := by
        field_simp
        linarith
      have r2: (y + z) / (u + x) = -1 := by
        field_simp
        linarith
      have r3: (z + u) / (x + y) = -1 := by
        field_simp
        linarith
      have r4: (u + x) / (y + z) = -1 := by
        field_simp
        linarith
      left
      simp [r1, r2, r3, r4]
      norm_num
      