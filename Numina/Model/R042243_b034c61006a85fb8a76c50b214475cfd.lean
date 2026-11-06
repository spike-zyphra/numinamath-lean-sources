import Mathlib

theorem algebra_12266 {u v w : ℝ} (hu : 0 < u ∧ u ≠ 1) (hv : 0 < v ∧ v ≠ 1) (hw : 0 < w ∧ w ≠ 1)
    (h1 : Real.logb u (v * w) + Real.logb v w = 5) (h2 : Real.logb v u + Real.logb w v = 3) :
    Real.logb w u = 4 / 5 := by
  have hu1 : 0 < u := hu.1
  have hu2 : u ≠ 1 := hu.2
  have hv1 : 0 < v := hv.1
  have hv2 : v ≠ 1 := hv.2
  have hw1 : 0 < w := hw.1
  have hw2 : w ≠ 1 := hw.2
  have h1' : Real.logb u (v * w) = (Real.log (v * w) ) / Real.log u := by 
    field_simp [Real.logb]
  have h1'' : Real.logb v w = Real.log w / Real.log v := by 
    field_simp [Real.logb]
  have h2' : Real.logb v u = Real.log u / Real.log v := by 
    field_simp [Real.logb]
  have h2'' : Real.logb w v = Real.log v / Real.log w := by 
    field_simp [Real.logb]
  have h3 : Real.logb w u = Real.log u / Real.log w := by 
    field_simp [Real.logb]
  rw [h1', h1''] at h1 
  rw [h2', h2''] at h2
  rw [h3]
  have h11 : Real.log (v * w) = Real.log v + Real.log w := by 
    rw [Real.log_mul (by linarith) (by linarith)]
  rw [h11] at h1 
  have eq1 : Real.log v ^ 2 + Real.log v * Real.log w + Real.log u * Real.log w - 5 * Real.log u * Real.log v = 0 := by 
    field_simp [(show Real.log u ≠ 0 by
      by_contra h0 
      have : Real.log u = 0 := by linarith 
      have h4 : u = 1 := by 
        rw [Real.log_eq_zero] at this 
        rcases this with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      tauto 
    ), (show Real.log v ≠ 0 by
      by_contra h0 
      have : Real.log v = 0 := by linarith 
      have h5 : v = 1 := by 
        rw [Real.log_eq_zero] at this 
        rcases this with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      tauto 
    )] at h1 ⊢
    nlinarith 
  have eq2 : Real.log u * Real.log w + Real.log v ^ 2 = 3 * Real.log v * Real.log w := by 
    field_simp [(show Real.log v ≠ 0 by 
      by_contra h0 
      have : Real.log v = 0 := by linarith 
      have h5 : v = 1 := by 
        rw [Real.log_eq_zero] at this 
        rcases this with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      tauto 
    ), (show Real.log w ≠ 0 by 
      by_contra h0 
      have : Real.log w = 0 := by linarith 
      have h6 : w = 1 := by 
        rw [Real.log_eq_zero] at this 
        rcases this with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      tauto 
    )] at h2 ⊢ 
    nlinarith 
  have h4 : 5 * Real.log u = 4 * Real.log w := by 
    have h5 : Real.log v * (4 * Real.log w - 5 * Real.log u) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h5) with h6 h7 
    · -- Real.log v = 0 
      have h0 : Real.log v = 0 := h6 
      have h51 : v = 1 := by 
        rw [Real.log_eq_zero] at h0 
        rcases h0 with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      have h52 : v = 1 := h51 
      have h53 : v ≠ 1 := hv2 
      contradiction 
    · -- 4 * Real.log w - 5 * Real.log u = 0 
      linarith 
  have h5 : Real.log u / Real.log w = 4 / 5 := by 
    have h50 : Real.log w ≠ 0 := by 
      by_contra h0 
      have : Real.log w = 0 := by linarith 
      have h61 : w = 1 := by 
        rw [Real.log_eq_zero] at this 
        rcases this with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      tauto 
    have h44 : 5 * Real.log u = 4 * Real.log w := h4 
    field_simp [h50] 
    linarith 
  linarith