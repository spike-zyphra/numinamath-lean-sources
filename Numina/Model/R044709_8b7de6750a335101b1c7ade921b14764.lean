import Mathlib

theorem inequalities_86997 (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) :
    4 ≤ (a 0 + a 2) / (a 0 + a 1) + (a 1 + a 3) / (a 1 + a 2) +
        (a 2 + a 0) / (a 2 + a 3) + (a 3 + a 1) / (a 3 + a 0) := by
  have ha1 : 0 < a 0 := ha 0
  have ha2 : 0 < a 1 := ha 1
  have ha3 : 0 < a 2 := ha 2
  have ha4 : 0 < a 3 := ha 3
  have h1 : 0 < (a 0 + a 1) := by positivity
  have h2 : 0 < (a 1 + a 2) := by positivity
  have h3 : 0 < (a 2 + a 3) := by positivity
  have h4 : 0 < (a 3 + a 0) := by positivity
  have h5 : (a 0 + a 2) / (a 0 + a 1) + (a 1 + a 3) / (a 1 + a 2) + (a 2 + a 0) / (a 2 + a 3) + (a 3 + a 1) / (a 3 + a 0) - 4 ≥ 0 := by
    have pos1 : 0 < (a 0 + a 1) := by positivity
    have pos2 : 0 < (a 1 + a 2) := by positivity
    have pos3 : 0 < (a 2 + a 3) := by positivity
    have pos4 : 0 < (a 3 + a 0) := by positivity
    have h6 : (a 0 + a 2) / (a 0 + a 1) + (a 1 + a 3) / (a 1 + a 2) + (a 2 + a 0) / (a 2 + a 3) + (a 3 + a 1) / (a 3 + a 0) - 4 =
        ((a 0 + a 2) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0) + 
         (a 1 + a 3) * (a 0 + a 1) * (a 2 + a 3) * (a 3 + a 0) + 
         (a 2 + a 0) * (a 0 + a 1) * (a 1 + a 2) * (a 3 + a 0) + 
         (a 3 + a 1) * (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) - 
         4 * (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0)) / ((a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0)) := by 
      field_simp
      <;> ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 0 - a 3), sq_nonneg (a 1 - a 2), sq_nonneg (a 1 - a 3), sq_nonneg (a 2 - a 3),
      sq_nonneg (a 0 + a 1 - a 2 - a 3), sq_nonneg (a 1 + a 2 - a 3 - a 0), 
      mul_pos ha1 ha2, mul_pos ha1 ha3, mul_pos ha1 ha4, 
      mul_pos ha2 ha3, mul_pos ha2 ha4, 
      mul_pos ha3 ha4
    ]
    positivity
  linarith