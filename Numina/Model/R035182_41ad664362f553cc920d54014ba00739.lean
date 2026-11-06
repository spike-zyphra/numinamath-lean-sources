import Mathlib

theorem algebra_19928 (P : ℝ × ℝ) (hP : P = (6, 0)) (line : ℝ → ℝ) (hline : line = fun x => 2 * x - 2) :
    IsLeast {d | ∃ x, d = Real.sqrt ((x - P.1)^2 + (line x - P.2)^2)} (2 * Real.sqrt 5) := by
  rw [hP] at *
  rw [hline] at *
  constructor
  · -- Show that 2 * sqrt 5 is in the set
    use 2
    have h1 : Real.sqrt ((2 - (6 : ℝ))^2 + (2 * (2 : ℝ) - 2 - (0 : ℝ))^2) = 2 * Real.sqrt 5 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    linarith [h1]
  · -- Show that 2 * sqrt 5 is the least in the set
    intro d
    rintro ⟨x, hx⟩
    have h2 : Real.sqrt ((x - (6 : ℝ))^2 + (2 * x - 2 - (0 : ℝ))^2) ≥ 2 * Real.sqrt 5 := by
      have h3 : (x - (6 : ℝ))^2 + (2 * x - 2 - (0 : ℝ))^2 ≥ (20 : ℝ) := by
        nlinarith [sq_nonneg (x - (2 : ℝ))]
      have h4 : Real.sqrt ((x - (6 : ℝ))^2 + (2 * x - 2 - (0 : ℝ))^2) ≥ Real.sqrt (20 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h5 : Real.sqrt (20 : ℝ) = 2 * Real.sqrt 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      nlinarith [h4, h5]
    have h3 : Real.sqrt ((x - (6 : ℝ))^2 + (2 * x - 2 - (0 : ℝ))^2) = d := by
      linarith [hx]
    linarith [h2, h3]