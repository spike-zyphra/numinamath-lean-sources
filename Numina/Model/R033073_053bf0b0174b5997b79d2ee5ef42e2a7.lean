import Mathlib

theorem algebra_258647 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hne : u ≠ 1 ∧ v ≠ 1 ∧ w ≠ 1) (h1 : Real.logb u (v * w) + Real.logb v w = 5)
    (h2 : Real.logb v u + Real.logb w v = 3) :
    Real.logb w u = 4 / 5 := by
  have hu1 : u ≠ 1 := hne.1
  have hv1 : v ≠ 1 := hne.2.1
  have hw1 : w ≠ 1 := hne.2.2
  have eq1 : Real.logb u (v * w) = (Real.log (v * w) ) / Real.log u := by
    field_simp [Real.logb]
  have eq2 : Real.logb v w = Real.log w / Real.log v := by
    field_simp [Real.logb]
  have eq3 : Real.log (v * w) = Real.log v + Real.log w := by
    rw [Real.log_mul (by linarith) (by linarith)]
  have eq4 : Real.logb v u = Real.log u / Real.log v := by
    field_simp [Real.logb]
  have eq5 : Real.logb w v = Real.log v / Real.log w := by
    field_simp [Real.logb]
  have eq6 : Real.logb w u = Real.log u / Real.log w := by
    field_simp [Real.logb]
  rw [eq1, eq2, eq3] at h1
  rw [eq4, eq5] at h2
  have h3 : Real.log u ≠ 0 := by
    by_contra h
    have h4 : Real.log u = 0 := by
      linarith
    have h5 : u = 1 := by
      rw [Real.log_eq_zero] at h4
      rcases h4 with (r | r | r)
      · linarith
      · linarith
      · linarith
    have h6 : u = 1 := h5
    have h7 : u ≠ 1 := hne.1
    contradiction
  have h4 : Real.log v ≠ 0 := by
    by_contra h
    have h5 : Real.log v = 0 := by
      linarith
    have h6 : v = 1 := by
      rw [Real.log_eq_zero] at h5
      rcases h5 with (r | r | r)
      · linarith
      · linarith
      · linarith
    have h7 : v = 1 := h6
    have h8 : v ≠ 1 := hne.2.1
    contradiction
  have h5 : Real.log w ≠ 0 := by
    by_contra h
    have h6 : Real.log w = 0 := by
      linarith
    have h7 : w = 1 := by
      rw [Real.log_eq_zero] at h6
      rcases h6 with (r | r | r)
      · linarith
      · linarith
      · linarith
    have h8 : w = 1 := h7
    have h9 : w ≠ 1 := hne.2.2
    contradiction
  have eq7 : (Real.log v + Real.log w) * Real.log v + (Real.log u) * (Real.log w) = 5 * (Real.log u) * (Real.log v) := by
    have eq8 : Real.log v ≠ 0 := h4
    have eq9 : Real.log u ≠ 0 := h3
    field_simp at h1 ⊢
    nlinarith
  have eq8 : (Real.log u) * (Real.log w) + (Real.log v) ^ 2 = 3 * (Real.log v) * (Real.log w) := by
    have eq10 : Real.log v ≠ 0 := h4
    have eq11 : Real.log w ≠ 0 := h5
    field_simp at h2 ⊢
    nlinarith
  rw [eq6]
  have h11 : Real.log u = 4 / 5 * Real.log w := by
    nlinarith [sq_pos_of_ne_zero (show Real.log v ≠ 0 by exact h4), sq_pos_of_ne_zero (show Real.log u ≠ 0 by exact h3), sq_pos_of_ne_zero (show Real.log w ≠ 0 by exact h5),
      sq_nonneg (Real.log v - Real.log w), sq_nonneg (Real.log u - Real.log v), sq_nonneg (Real.log v - 2), sq_nonneg (Real.log w - 2), sq_nonneg (Real.log u - 4)
    ]
  field_simp [h5]
  linarith [h11]