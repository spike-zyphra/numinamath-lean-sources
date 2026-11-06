import Mathlib

open Real

theorem algebra_94341 {x : ℝ} (a : ℕ → ℝ) {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (ha0 : a 0 = sin x) (ha1 : a 1 = cos x) (ha2 : a 2 = tan x)
    (h_cos : cos x ≠ 0) :
    a 7 = 1 + cos x := by
  have h1 : sin x ≠ 0 := by
    by_contra h
    have h0 : sin x = 0 := h
    have h4 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h0] at h4
    have h66 : cos x = 0 := by
      have h77 : a 1 = cos x := by
        simpa using ha1
      have h88 : a 1 = 0 := by
        rw [ha 1]
        rw [ha0]
        rw [h0]
        all_goals norm_num
      linarith [h77, h88]
    have h77 : cos x ^ 2 = 1 := by
      nlinarith [h4]
    have h99 : cos x ^ 2 = 0 := by
      rw [h66]
      norm_num
    nlinarith [h77, h99]
  have h2 : r = cos x / sin x := by
    have h3 : a 1 = a 0 * r ^ 1 := ha 1
    rw [ha0] at h3
    rw [ha1] at h3
    field_simp [h1] at h3 ⊢
    all_goals linarith [h3]
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  have h5 : cos x ^ 3 = sin x ^ 2 := by
    have eq2 : a 2 = a 0 * r ^ 2 := ha 2
    rw [ha0] at eq2
    rw [ha2] at eq2
    rw [h2] at eq2
    field_simp [h1, h_cos, htan] at eq2 ⊢
    have h551 : sin x ^ 3 = sin x * cos x ^ 3 := by
      have eq4 : sin x * sin x ^ 2 = sin x * cos x ^ 2 * cos x := by
        nlinarith [eq2]
      nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (sin x ^ 2 - cos x ^ 2)]
    have h552 : sin x ^ 2 = cos x ^ 3 := by
      have h6 : sin x ≠ 0 := h1
      have h7 : sin x ^ 3 = sin x * cos x ^ 3 := h551
      have : sin x ^ 2 = cos x ^ 3 := by
        apply (mul_left_inj' (show sin x ≠ 0 by exact h1)).mp
        linarith
      assumption
    nlinarith
  -- Now compute $a_7$
  have eq3 : a 7 = 1 + cos x := by
    have eq4 : a 7 = a 0 * r ^ 7 := ha 7
    rw [ha0, h2] at eq4
    have eq5 : a 7 = sin x * (cos x / sin x) ^ 7 := by
      linarith [eq4]
    have h553 : sin x * (cos x / sin x) ^ 7 = cos x ^ 7 / sin x ^ 6 := by
      field_simp [h1]
      <;> ring_nf 
    rw [h553] at eq5
    have h555 : cos x ^ 7 = cos x * sin x ^ 4 := by
      calc
        cos x ^ 7 = cos x ^ 7 := by rfl
        _ = cos x * (cos x ^ 3) ^ 2 := by ring_nf
        _ = cos x * (sin x ^ 2) ^ 2 := by rw [h5]
        _ = cos x * sin x ^ 4 := by ring_nf
    have h556 : cos x ^ 7 / sin x ^ 6 = cos x / sin x ^ 2 := by
      rw [h555]
      field_simp [h1]
      <;> ring_nf 
    have h557 : cos x / sin x ^ 2 = 1 + cos x := by
      have h66 : (1 + cos x) * sin x ^ 2 = cos x := by 
        have h6 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        nlinarith [sq_nonneg (cos x ^ 2 - 1), sq_nonneg (cos x - 1), sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - sin x ^ 2), sq_nonneg (cos x ^ 2 - 1), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (sin x ^ 2 - 0)]
      have h77 : sin x ^ 2 = cos x / (1 + cos x) := by
        field_simp [(show 1 + cos x ≠ 0 by 
          by_contra h
          have : cos x = -1 := by nlinarith
          have h6 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          nlinarith [sq_nonneg (sin x ^ 2), sq_pos_of_ne_zero h1]
        )] at h66 ⊢
        nlinarith
      rw [h77]
      field_simp [(show 1 + cos x ≠ 0 by 
          by_contra h
          have : cos x = -1 := by nlinarith
          have h6 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          nlinarith [sq_nonneg (sin x ^ 2), sq_pos_of_ne_zero h1]
      ), h1, h_cos]
    nlinarith [eq5, h556, h557]
  linarith [eq3]