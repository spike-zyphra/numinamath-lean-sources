import Mathlib

theorem algebra_602314 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsLeast {(x : ℝ) | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) * (a + b + c)} 100 := by

  constructor
  · -- First, prove that 100 belongs to the set
    use 2, 2, 1
    norm_num
  · -- Then, prove that no value less than 100 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq⟩
    have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc

    rw [h_eq]
    have h2 : ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) * (a + b + c) ≥ 100 := by
      have h3 : ((a + b)^2 + (a + b + 4 * c)^2) * (a + b + c) ≥ 100 * (a * b * c) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 4 * c), sq_nonneg (a + b - 2 * c), 
          sq_nonneg (a * b - 4 * b * c), sq_nonneg (a * b - 4 * a * c), 
          sq_nonneg (a * c - b * c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h4 : ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) * (a + b + c) = ((a + b)^2 + (a + b + 4 * c)^2) * (a + b + c) / (a * b * c) := by
        ring_nf
      have h5 : ((a + b)^2 + (a + b + 4 * c)^2) * (a + b + c) / (a * b * c) ≥ (100 * (a * b * c)) / (a * b * c) := by 
        apply (div_le_div_right (by positivity)).mpr h3
      have h6 : (100 * (a * b * c)) / (a * b * c) = 100 := by 
        field_simp [show 0 < a * b * c by positivity]
        <;> nlinarith
      linarith [h4, h5, h6]
    linarith