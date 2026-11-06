import Mathlib

theorem algebra_201451 {x y z : ℝ} (hzz : x * y * z ≠ 0) (hxy : 2 * x * y = 3 * y * z)
    (hxyz : 3 * y * z = 5 * x * z) (c : ℝ) (hc : c = (x + 3 * y - 3 * z) / (x + 3 * y - 6 * z)) :
    c = 2 := by

  have hx1 : x ≠ 0 := by
    by_contra h
    have h0 : x * y * z = 0 := by
      rw [h]
      norm_num
    contradiction

  have hy1 : y ≠ 0 := by
    by_contra h
    have h0 : x * y * z = 0 := by
      rw [h]
      norm_num
    contradiction

  have hz1 : z ≠ 0 := by
    by_contra h
    have h0 : x * y * z = 0 := by
      rw [h]
      norm_num
    contradiction

  have eq1 : 2 * x = 3 * z := by
    have h1 : 2 * x * y = 3 * y * z := by
      linarith [hxy]
    have h2 : y ≠ 0 := hy1
    apply (mul_left_inj' h2).mp
    linarith

  -- From 3y * z = 5x * z => y = 5/3 x
  have eq2 : 3 * y = 5 * x := by
    have h2 : 3 * y * z = 5 * x * z := by
      linarith [hxyz]
    have h3 : z ≠ 0 := hz1
    apply (mul_right_inj' h3).mp
    linarith

  have eq3 : z = (2 / 3) * x := by
    linarith [eq1]

  have eq4 : y = (5 / 3) * x := by
    linarith [eq2]

  have eq5 : x + 3 * y - 3 * z = 4 * x := by
    rw [eq4, eq3]
    linarith

  have eq6 : x + 3 * y - 6 * z = 2 * x := by
    rw [eq4, eq3]
    linarith

  have h7 : (x + 3 * y - 3 * z) / (x + 3 * y - 6 * z) = 2 := by
    have h8 : x + 3 * y - 6 * z = 2 * x := eq6
    rw [h8]
    have h9 : x + 3 * y - 3 * z = 4 * x := eq5
    rw [h9]
    have h10 : x ≠ 0 := hx1
    field_simp [show x ≠ 0 by exact h10]
    <;> ring_nf <;> linarith

  rw [hc]
  exact h7