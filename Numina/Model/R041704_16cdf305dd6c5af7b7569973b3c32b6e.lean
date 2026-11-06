import Mathlib
open Real Set

theorem algebra_8985 {f : ℝ → ℝ} (hf : f = λ x => log x / x) :
    IsGreatest (image f (Ioi 0)) (1 / exp 1) := by
  constructor
  · -- Show that (1 / exp 1) is attained by f over (0, ∞)
    rw [mem_image]
    use exp 1
    constructor
    · -- Show that exp 1 is in (0, ∞)
      simp
      all_goals linarith [Real.exp_pos 1]
    · -- Show that f (exp 1) = 1 / exp 1
      rw [hf]
      simp
      all_goals linarith [Real.exp_pos 1]
  · -- Show that (1 / exp 1) is an upper bound for the image
    intro y hy
    rw [mem_image] at hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : 0 < x := by
      simpa using hx
    have h1 : log x / x = y := by
      simpa [hf] using hfx
    have h2 : log x / x ≤ 1 / exp 1 := by
      have h17 : x > 0 := hx1
      have h3 : log (x / exp 1) ≤ (x / exp 1 - 1 : ℝ) := by
        apply log_le_sub_one_of_pos
        positivity
      have h4 : log (x / exp 1) = log x - log (exp 1) := by
        rw [log_div (by linarith) (by positivity)]
      have h5 : log (exp 1) = (1 : ℝ) := by 
        rw [log_exp]
      have h6 : log x - 1 ≤ x / exp 1 - 1 := by
        have h7 : log x - log (exp 1) ≤ (x / exp 1 - 1 : ℝ) := by 
          linarith [h3, h4, h5]
        linarith [h5, h7]
      have h7 : log x ≤ x / exp 1 := by
        linarith [h6]
      have h9 : 0 < x := hx1
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h10 : log x ≤ x / exp 1 := h7
      have h14 : log x * exp 1 ≤ x := by
        have h14 : log x ≤ x / exp 1 := h7
        have h11 : (log x : ℝ) * exp 1 ≤ (x / exp 1 : ℝ) * exp 1 := by
          have h14 : log x ≤ x / exp 1 := h7
          nlinarith [Real.exp_pos 1, h14, Real.exp_pos 1]
        have h13 : (x / exp 1 : ℝ) * exp 1 = (x : ℝ) := by
          field_simp [Real.exp_pos 1]
        linarith [h11, h13]
      nlinarith [Real.exp_pos 1, Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
    have ht : y = log x / x := by
      linarith [h1]
    linarith [ht, h2]