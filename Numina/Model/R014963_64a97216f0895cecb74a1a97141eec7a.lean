import Mathlib

theorem algebra_254174 (x : ℝ) (hx : x ≠ 0) (h : 5 * x = 3 * (x / (1 - y / 100))) :
    y = 40 := by

  have h1 : 1 - y / 100 ≠ 0 := by
    by_contra h2
    have h3 : x / (1 - y / 100) = 0 := by
      rw [show 1 - y / 100 = 0 by linarith]
      norm_num
      all_goals linarith
    rw [h3] at h
    have h4 : 5 * x = 0 := by linarith
    have h5 : x = 0 := by
      linarith
    contradiction

  have eq3 : x / (1 - y / 100) = x * 100 / (100 - y) := by
    have h2 : (1 - y / 100 : ℝ) = (100 - y) / 100 := by
      field_simp
      <;> ring
      <;> field_simp
    rw [h2]
    <;> field_simp [(show (100 - y : ℝ) ≠ 0 by
      by_contra h3
      have h4 : y = 100 := by linarith
      have h5 : 1 - y / 100 = 0 := by
        rw [h4]
        norm_num
      tauto
    ), hx]
    <;> ring

  rw [eq3] at h

  have eq4 : 5 * x * (100 - y) = 300 * x := by
    have h2 : 100 - y ≠ 0 := by
      by_contra h3
      have h4 : y = 100 := by linarith
      have h5 : 1 - y / 100 = 0 := by
        rw [h4]
        norm_num
      tauto
    have h3 : 5 * x = 3 * (x * 100 / (100 - y)) := h
    have h4 : 5 * x * (100 - y) = 3 * (x * 100) := by
      have h5 : 100 - y ≠ 0 := h2
      have eq6 : 3 * (x * 100 / (100 - y)) = 3 * (x * 100) / (100 - y) := by
        ring_nf
      rw [eq6] at h3
      have eq7 : 5 * x * (100 - y) = 3 * (x * 100) := by
        have h8 : 100 - y ≠ 0 := h5
        field_simp [h8] at h3 ⊢
        <;> nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero h8]
      linarith
    linarith

  have eq5 : 5 * (100 - y) = 300 := by
    apply (mul_left_inj' hx).mp
    linarith

  have eq6 : 100 - y = 60 := by
    linarith

  linarith