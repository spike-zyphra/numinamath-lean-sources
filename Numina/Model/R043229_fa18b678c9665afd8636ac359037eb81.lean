import Mathlib

theorem inequalities_44839 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a * b + b * c + 1 / (c * a)) * (b * c + c * a + 1 / (a * b)) *
    (c * a + a * b + 1 / (b * c)) ≥ (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) := by
  have h1 : 1 / (c * a) = b := by 
    have h1 : a * b * c = 1 := habc
    field_simp
    nlinarith [h1]
  have h2 : 1 / (a * b) = c := by 
    have h1 : a * b * c = 1 := habc
    field_simp
    nlinarith [h1]
  have h3 : 1 / (b * c) = a := by 
    have h1 : a * b * c = 1 := habc
    field_simp
    nlinarith [h1]
  have eq1 : a * b + b * c + 1 / (c * a) = b * (a + c + 1) := by
    rw [h1]
    ring
  have eq2 : b * c + c * a + 1 / (a * b) = c * (a + b + 1) := by
    rw [h2]
    ring
  have eq3 : c * a + a * b + 1 / (b * c) = a * (b + c + 1) := by
    rw [h3]
    ring
  have eq4 : (b * (a + c + 1)) * (c * (a + b + 1)) * (a * (b + c + 1)) = 
          (a * b * c) * (a + b + 1) * (a + c + 1) * (b + c + 1) := by 
    ring
  rw [eq1, eq2, eq3]
  rw [eq4] at *
  rw [habc] at *
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          habc
        ]