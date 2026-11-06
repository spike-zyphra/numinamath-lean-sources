import Mathlib

theorem algebra_221081 (a b c : ℝ) (h : a ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 2 + b * x + c) (h1 : f ((a - b - c) / (2 * a)) = 0) :
    f (-1) = 0 ∨ f 1 = 0 := by 
  have eq1 : a * ((a - b - c) / (2 * a)) ^ 2 + b * ((a - b - c) / (2 * a)) + c = 0 := by 
    rw [hf ((a - b - c) / (2 * a))] at h1 
    linarith 
  have eq2 : (a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * c * a = 0 := by
    have h2 : a * ((a - b - c) / (2 * a)) ^ 2 + b * ((a - b - c) / (2 * a)) + c = 0 := eq1
    have eq3 : a * ((a - b - c) / (2 * a)) ^ 2 + b * ((a - b - c) / (2 * a)) + c =
          ((a - b - c) ^ 2) / (4 * a) + (b * (a - b - c)) / (2 * a) + c := by
      field_simp
      ring 
    rw [eq3] at h2 
    have eq4 : (a - b - c : ℝ) ^ 2 + 2 * b * (a - b - c) + 4 * c * a = 0 := by 
      have eq5 : ((a - b - c) ^ 2) / (4 * a) + (b * (a - b - c)) / (2 * a) + c = 0 := by 
        simpa using h2 
      have eq5a : a ≠ 0 := h 
      have eq6 : (a - b - c : ℝ) ^ 2 + 2 * b * (a - b - c) + 4 * c * a = 0 := by 
        have eq7 : ((a - b - c) ^ 2) / (4 * a) + (b * (a - b - c)) / (2 * a) + c = 0 := eq5 
        have eq8 : ((a - b - c) ^ 2) / (4 * a) + (b * (a - b - c)) / (2 * a) + c = 
          ((a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * c * a) / (4 * a) := by 
          field_simp
          ring 
        rw [eq8] at eq7 
        have eq9 : ((a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * c * a) / (4 * a) = 0 := by 
          linarith [eq7] 
        have eq10 : (a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * c * a = 0 := by 
          have eq11 : ((a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * c * a) / (4 * a) = 0 := eq9 
          have eq12 : ((a - b - c) ^ 2 + 2 * b * (a - b - c) + 4 * c * a) = 0 := by 
            have eq13 : (4 * a) ≠ 0 := by 
              intro h'
              apply h 
              linarith 
            field_simp [eq13] at eq11 
            all_goals linarith 
          linarith
        linarith 
      linarith 
    linarith 
  have eq3 : f (-1) = a - b + c := by 
    rw [hf]
    ring 
  have eq4 : f 1 = a + b + c := by 
    rw [hf]
    ring 
  have eq5 : (a + c - b) * (a + c + b) = 0 := by 
    nlinarith [eq2] 
  cases' (mul_eq_zero.mp eq5) with h3 h4 
  · -- Case where a + c - b = 0 
    left 
    have eq6 : b = a + c := by linarith 
    rw [eq3] 
    rw [eq6]
    all_goals linarith 
  · -- Case where a + c + b = 0 
    right 
    have eq7 : b = -a - c := by linarith 
    rw [eq4] 
    rw [eq7]
    all_goals linarith