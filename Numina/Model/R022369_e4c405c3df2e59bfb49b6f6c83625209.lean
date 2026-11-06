import Mathlib

theorem algebra_880 {a b c : ℝ} (hnonzero : a * b * c ≠ 0) (h1 : (a + b - c) / c = (a - b + c) / b)
    (h2 : (a - b + c) / b = (-a + b + c) / a) : ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 ∨ ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 := by

  have ha : a ≠ 0 := by
    by_contra h
    have : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction

  have hb : b ≠ 0 := by
    by_contra h
    have : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction

  have hc : c ≠ 0 := by
    by_contra h
    have : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction

  have eq1 : b * (a + b - c) = c * (a - b + c) := by
    have h1' : (a + b - c) / c = (a - b + c) / b := h1
    field_simp [hc, hb] at h1' ⊢
    linarith

  have eq2 : a * (a - b + c) = b * (-a + b + c) := by
    have h2' : (a - b + c) / b = (-a + b + c) / a := h2
    field_simp [hb, ha] at h2' ⊢
    linarith

  have eq3 : (b - c) * (a + b + c) = 0 := by 
    linarith [eq1]

  have eq4 : (a - b) * (a + b + c) = 0 := by 
    linarith [eq2]

  by_cases h : a + b + c = 0

  · -- Case where a + b + c = 0
    have h3 : (a + b) * (b + c) * (c + a) = - (a * b * c) := by
      have ha1 : a + b = -c := by linarith
      have hb1 : b + c = -a := by linarith
      have hc1 : c + a = -b := by linarith
      rw [ha1, hb1, hc1]
      ring

    have h4 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 := by
      rw [h3]
      field_simp [hnonzero]

    right
    exact h4

  · -- Case where a + b + c ≠ 0
    have hne : a + b + c ≠ 0 := by exact h

    have eq5 : b - c = 0 := by
      apply (mul_left_inj' hne).mp
      linarith [eq3]

    have eq6 : b = c := by linarith

    have eq7 : a - b = 0 := by 
      apply (mul_left_inj' hne).mp
      linarith [eq4]

    have eq8 : a = b := by linarith

    have eq9 : a = c := by linarith [eq8, eq6]

    have h3 : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := by 
      rw [show b = a by linarith [eq8], show c = a by linarith [eq9]]
      ring_nf

    have h4 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 := by 
      rw [h3]
      field_simp [hnonzero]
      <;> nlinarith

    left
    exact h4