import Mathlib

theorem algebra_318667 {x y z : ℝ} (h1 : x * y / (x + y) = 2) (h2 : x * z / (x + z) = 3) (h3 : y * z / (y + z) = 4) :
7 * x + 5 * y - 2 * z = 0:= by

  have h4 : x + y ≠ 0 := by
    by_contra h
    have : x * y / (x + y) = 0 := by
      rw [h]
      norm_num
    linarith

  have h5 : x + z ≠ 0 := by
    by_contra h
    have : x * z / (x + z) = 0 := by
      rw [h]
      norm_num
    linarith

  have h6 : y + z ≠ 0 := by
    by_contra h
    have : y * z / (y + z) = 0 := by
      rw [h]
      norm_num
    linarith

  have eq11 : x ≠ 0 := by
    by_contra hx
    rw [hx] at h1
    field_simp [show y ≠ 0 by
      by_contra hy
      have : y = 0 := by linarith
      have h13 : x + y = 0 := by
        rw [show x = 0 by linarith, show y = 0 by linarith]
        norm_num
      contradiction
    ] at h1

  have eq12 : y ≠ 0 := by
    by_contra hy
    rw [hy] at h1
    field_simp [show x ≠ 0 by
      by_contra hx
      have : x = 0 := by linarith
      have h13 : x + y = 0 := by
        rw [show x = 0 by linarith, show y = 0 by linarith]
        norm_num
      contradiction
    ] at h1

  have eq13 : z ≠ 0 := by
    by_contra hz
    rw [hz] at h2
    field_simp [show x ≠ 0 by
      by_contra hx
      have : x = 0 := by linarith
      have h13 : x + z = 0 := by
        rw [show x = 0 by linarith, show z = 0 by linarith]
        norm_num
      contradiction
    ] at h2

  have eq1 : 1 / x + 1 / y = 1 / 2 := by
    have eq2 : x * y = 2 * (x + y) := by
      have h11 : x * y / (x + y) = 2 := h1
      have h4' : x + y ≠ 0 := h4
      field_simp at h11 ⊢
      linarith
    have hx1 : x ≠ 0 := eq11
    have hy1 : y ≠ 0 := eq12
    field_simp at *
    nlinarith

  have eq2 : 1 / x + 1 / z = 1 / 3 := by
    have eq22 : x * z = 3 * (x + z) := by
      have h22 : x * z / (x + z) = 3 := h2
      have h5' : x + z ≠ 0 := h5
      field_simp at h22 ⊢
      linarith
    have hx1 : x ≠ 0 := eq11
    have hz1 : z ≠ 0 := eq13
    field_simp at *
    nlinarith

  have eq3 : 1 / y + 1 / z = 1 / 4 := by
    have eq22 : y * z = 4 * (y + z) := by
      have h33 : y * z / (y + z) = 4 := h3
      have h6' : y + z ≠ 0 := h6
      field_simp at h33 ⊢
      linarith
    have hy1 : y ≠ 0 := eq12
    have hz1 : z ≠ 0 := eq13
    field_simp at *
    nlinarith

  have eq4 : 1 / y - 1 / z = 1 / 6 := by
    linarith [eq1, eq2, eq3]

  have eq5 : 1 / y = 5 / 24 := by
    have eq5a : 1 / y + 1 / z = 1 / 4 := eq3
    have eq5b : 1 / y - 1 / z = 1 / 6 := eq4
    linarith

  have eq6 : 1 / z = 1 / 24 := by
    linarith [eq3, eq5]

  have eq7 : 1 / x = 7 / 24 := by
    linarith [eq1, eq5]

  have hx24 : x = 24 / 7 := by
    have h14 : 1 / x = 7 / 24 := eq7
    have hx1 : x ≠ 0 := eq11
    field_simp at h14
    linarith

  have hy24 : y = 24 / 5 := by 
    have h14 : 1 / y = 5 / 24 := eq5
    have hy1 : y ≠ 0 := eq12
    field_simp at h14
    linarith

  have hz24 : z = 24 := by 
    have h14 : 1 / z = 1 / 24 := eq6
    have hz1 : z ≠ 0 := eq13
    field_simp at h14
    linarith

  rw [hx24, hy24, hz24]
  norm_num