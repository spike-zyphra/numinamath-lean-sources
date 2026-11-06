import Mathlib

theorem algebra_218207 {a b : ℕ} (ha : a > 1) (hb : b > 1)
    (h : ∃ d, Real.logb b a = Real.logb (2 * b) (2 * a) - d ∧
      Real.logb (2 * b) (2 * a) = Real.logb (4 * b) (4 * a) - d) :
    a = b := by
  rcases h with ⟨d, h₁, h₂⟩
  have h3 : Real.logb b a + Real.logb (4 * b) (4 * a) = 2 * Real.logb (2 * b) (2 * a) := by linarith
  have h4 : Real.logb b a = Real.log a / Real.log b := by
    field_simp [Real.logb]
    all_goals (norm_num)
  have h5 : Real.logb (2 * b) (2 * a) = Real.log (2 * (a : ℝ)) / Real.log (2 * (b : ℝ)) := by
    field_simp [Real.logb]
    all_goals (norm_num)
  have h6 : Real.logb (4 * b) (4 * a) = Real.log (4 * (a : ℝ)) / Real.log (4 * (b : ℝ)) := by
    field_simp [Real.logb]
    all_goals (norm_num)
  have h7 : Real.log (2 * (a : ℝ)) = Real.log (2 : ℝ) + Real.log (a : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have h7' : Real.log (2 * (b : ℝ)) = Real.log (2 : ℝ) + Real.log (b : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have h8 : Real.log (4 * (a : ℝ)) = Real.log (4 : ℝ) + Real.log (a : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have h8' : Real.log (4 * (b : ℝ)) = Real.log (4 : ℝ) + Real.log (b : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have h9 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      simp [Real.log_pow]
  rw [h4, h5, h6, h7, h7', h8, h8', h9] at h3
  have h5 : Real.log (2 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals linarith
  have h9 : Real.log (a : ℝ) > 0 := by
    have ha2 : (a : ℝ) > 1 := by exact_mod_cast ha
    apply Real.log_pos
    linarith
  have h9b : Real.log (b : ℝ) > 0 := by
    have hb2 : (b : ℝ) > 1 := by exact_mod_cast hb
    apply Real.log_pos
    linarith
  have h10 : Real.log b > 0 := by positivity
  have h11 : Real.log (2 : ℝ) + Real.log b > 0 := by positivity
  have h12 : 2 * Real.log (2 : ℝ) + Real.log b > 0 := by positivity
  field_simp [h10, h11, h12] at h3
  <;> ring_nf at h3
  have h13 : (Real.log (2 : ℝ) ) * (Real.log (a : ℝ) - Real.log (b : ℝ) ) = 0 := by nlinarith
  cases (mul_eq_zero.mp h13) with
  | inl h14 =>
    linarith [Real.log_pos (show (2 : ℝ) > 1 by norm_num)]
  | inr h15 =>
    have h7 : (a : ℝ) = (b : ℝ) := by
      have h7 : Real.log (a : ℝ) = Real.log (b : ℝ) := by linarith
      have h8 : (a : ℝ) > 0 := by positivity
      have h9 : (b : ℝ) > 0 := by positivity
      have h10 : (a : ℝ) = (b : ℝ) := by
        have h11 : Real.log (a : ℝ) = Real.log (b : ℝ) := by linarith
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr h8) (Set.mem_Ioi.mpr h9) h11
      exact h10
    exact_mod_cast h7