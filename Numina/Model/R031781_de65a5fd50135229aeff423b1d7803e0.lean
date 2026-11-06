import Mathlib

open Real

theorem algebra_279704 {f : ℝ → ℝ} (hf : ∀ x, -1 < x ∧ x < 1 → f x = log ((1 + x) / (1 - x))) (x : ℝ) :
  -1 < x ∧ x < 1 →
    f ((3 * x + x ^ 3) / (1 + 3 * x ^ 2)) = 3 * f x := by 
  intro h 
  have h1 : -1 < x := h.1 
  have h2 : x < 1 := h.2 
  have hx1 : -1 < (3 * x + x ^ 3) / (1 + 3 * x ^ 2) := by 
    have h3 : 0 < 1 + 3 * x ^ 2 := by 
      nlinarith [sq_nonneg x] 
    apply (lt_div_iff₀ (by linarith [sq_nonneg x])).mpr 
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < x + 1 by linarith), pow_pos (show (0 : ℝ) < x + 1 by linarith) 3] 
  have hx3 : (3 * x + x ^ 3) / (1 + 3 * x ^ 2) < 1 := by 
    have h3 : 0 < 1 + 3 * x ^ 2 := by 
      nlinarith [sq_nonneg x] 
    apply (div_lt_iff₀ (by linarith [sq_nonneg x])).mpr 
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < (1 - x : ℝ) by linarith), pow_pos (show (0 : ℝ) < (1 - x : ℝ) by linarith) 3] 
  have h3 : f ((3 * x + x ^ 3) / (1 + 3 * x ^ 2)) = log ((1 + (3 * x + x ^ 3) / (1 + 3 * x ^ 2)) / (1 - (3 * x + x ^ 3) / (1 + 3 * x ^ 2))) := by 
    apply hf 
    constructor 
    · linarith [hx1] 
    · linarith [hx3] 
  have h4 : f x = log ((1 + x) / (1 - x)) := by 
    apply hf 
    constructor <;> linarith 
  rw [h3, h4] 
  have h5 : log ((1 + (3 * x + x ^ 3) / (1 + 3 * x ^ 2)) / (1 - (3 * x + x ^ 3) / (1 + 3 * x ^ 2))) = 3 * log ((1 + x) / (1 - x)) := by 
    have h6 : (1 + (3 * x + x ^ 3) / (1 + 3 * x ^ 2)) / (1 - (3 * x + x ^ 3) / (1 + 3 * x ^ 2)) = ((1 + x) / (1 - x)) ^ 3 := by 
      field_simp 
      ring_nf 
    rw [h6] 
    have h7 : log (((1 + x) / (1 - x)) ^ 3) = 3 * log ((1 + x) / (1 - x)) := by 
      simp [log_pow] 
    linarith [h7] 
  linarith [h5]