import Mathlib

theorem algebra_285274 {a b c A B C : ℝ} (ha : a + b + c = 0) (hA : A + B + C = 0)
    (hA_ne_0 : A ≠ 0) (hB_ne_0 : B ≠ 0) (hC_ne_0 : C ≠ 0)
    (h : a / A + b / B + c / C = 0) :
    {x : ℝ | x = a * A^2 + b * B^2 + c * C^2} = {0} := by

  have eq1 : a * B * C + b * A * C + c * A * B = 0 := by 
    have h1 : A ≠ 0 := hA_ne_0 
    have h2 : B ≠ 0 := hB_ne_0 
    have h3 : C ≠ 0 := hC_ne_0 
    have h4 : a / A + b / B + c / C = 0 := h 
    field_simp [h1, h2, h3] at h4 
    nlinarith 
  have eq4 : a * A^2 + b * B^2 + c * C^2 = 0 := by 
    have eq5 : c = -a - b := by linarith 
    have eq6 : C = -A - B := by linarith 
    have eq7 : a * A^2 + b * B^2 + c * C^2 = 
        a * A^2 + b * B^2 + (-a - b) * (-A - B)^2 := by 
      rw [eq5, eq6]
    -- Expanding 
    have eq10 : (-A - B)^2 = A^2 + 2 * A * B + B^2 := by 
      ring 
    have eq11 : a * A^2 + b * B^2 + (-a - b) * (-A - B)^2 =
        a * A^2 + b * B^2 + (-a - b) * (A^2 + 2 * A * B + B^2) := by 
      rw [eq10]
    have eq12 : a * A^2 + b * B^2 + (-a - b) * (A^2 + 2 * A * B + B^2) =
        a * A^2 + b * B^2 - a * (A^2 + 2 * A * B + B^2) - b * (A^2 + 2 * A * B + B^2) := by 
      ring
    have eq13 : a * A^2 + b * B^2 - a * (A^2 + 2 * A * B + B^2) - b * (A^2 + 2 * A * B + B^2) =
        -a * B^2 - b * A^2 - 2 * A * B * (a + b) := by 
      ring 
    -- Solving derivative:
    have eq14 : -a * B^2 - b * A^2 - 2 * A * B * (a + b) = 0 := by 
      have eq15 : a * B * C + b * A * C + c * A * B = 0 := eq1 
      have eq16 : c = -a - b := by linarith 
      have eq17 : C = -A - B := by linarith 
      rw [eq16, eq17] at eq15 
      nlinarith 
    -- Combine 
    rw [eq7, eq11, eq12, eq13] 
    linarith [eq14]
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- Assume x = a * A^2 + b * B^2 + c * C^2 
    intro h_eq 
    rw [eq4] at h_eq 
    linarith 
  · -- Assume x = 0 
    intro h_eq 
    rw [eq4, h_eq] 
    all_goals linarith