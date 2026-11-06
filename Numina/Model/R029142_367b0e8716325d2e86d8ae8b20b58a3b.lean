import Mathlib

theorem algebra_224126 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hne1 : u ≠ 1 ∧ v ≠ 1 ∧ w ≠ 1) (hlog : Real.logb u (v * w) + Real.logb v w = 5)
    (hlog' : Real.logb v u + Real.logb w v = 3) :
    Real.logb w u = 4 / 5 := by
  have hu1 : u ≠ 1 := hne1.1
  have hv1 : v ≠ 1 := hne1.2.1
  have hw1 : w ≠ 1 := hne1.2.2

  have eq1 : Real.logb u (v * w) = (Real.log v + Real.log w) / (Real.log u) := by 
    have h1 : Real.logb u (v * w) = (Real.log (v * w) ) / (Real.log u) := by 
      field_simp [Real.logb]
    have h2 : Real.log (v * w) = Real.log v + Real.log w := by 
      rw [Real.log_mul (by linarith) (by linarith)]
    rw [h1, h2]

  have eq2 : Real.logb v w = Real.log w / Real.log v := by 
    field_simp [Real.logb]

  have eq3 : Real.logb v u = Real.log u / Real.log v := by 
    field_simp [Real.logb]

  have eq4 : Real.logb w v = Real.log v / Real.log w := by 
    field_simp [Real.logb]

  rw [eq1, eq2] at hlog
  rw [eq3, eq4] at hlog'

  have h3 : Real.log u ≠ 0 := by
    by_contra h 
    have : u = 1 := by 
      rw [Real.log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith 
      · linarith 
      · linarith 
    contradiction

  have h4 : Real.log v ≠ 0 := by
    by_contra h 
    have : v = 1 := by 
      rw [Real.log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith 
      · linarith 
      · linarith 
    contradiction

  have h5 : Real.log w ≠ 0 := by 
    by_contra h 
    have : w = 1 := by 
      rw [Real.log_eq_zero] at h 
      rcases h with (r | r | r)
      · linarith 
      · linarith 
      · linarith 
    contradiction

  have eq6 : (Real.log v + Real.log w) * Real.log v + Real.log w * Real.log u = 5 * (Real.log u * Real.log v) := by 
    field_simp [h3, h4] at hlog 
    nlinarith

  have eq7 : Real.log u * Real.log w + Real.log v ^ 2 = 3 * (Real.log v * Real.log w) := by 
    field_simp [h4, h5] at hlog' 
    nlinarith

  have eq8 : (Real.log v + Real.log w) * Real.log v + Real.log w * Real.log u - (Real.log u * Real.log w + Real.log v ^ 2) = 5 * (Real.log u * Real.log v) - 3 * (Real.log v * Real.log w) := by 
    linarith [eq6, eq7]

  have eq9 : (Real.log w) * Real.log v + 3 * (Real.log v) * (Real.log w) - 5 * (Real.log u) * (Real.log v) = 0 := by 
    nlinarith [eq8]

  have eq10 : Real.log v * (4 * Real.log w - 5 * Real.log u) = 0 := by
    nlinarith [eq9]

  cases (mul_eq_zero.mp eq10) with 
  | inl h => 
    exfalso
    apply h4
    linarith
  | inr h => 
    have eq11 : 4 * Real.log w = 5 * Real.log u := by 
      linarith 
    have h6 : Real.logb w u = Real.log u / Real.log w := by
      field_simp [Real.logb]

    rw [h6]
    have h7 : Real.log u = 4 / 5 * Real.log w := by 
      linarith 
    rw [h7]
    field_simp [h5]
    <;> nlinarith