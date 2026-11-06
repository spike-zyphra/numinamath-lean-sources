import Mathlib

open Real Set
open scoped Real

theorem algebra_196686 (A : ℝ → ℝ)
  (hA : A = λ α => 1 / (sin α ^ 6 + cos α ^ 6)) :
  IsGreatest {x | ∃ α ∈ Icc 0 (π/2), A α = x} 4 := by
  constructor
  · -- Show 4 is attained, at π/4.
    use Real.pi / 4
    constructor
    · -- Show π/4 ∈ [0, π/2]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show A(π/4) = 4
      rw [hA]
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      simp only [h1, h2]
      have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h4 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = (1 / 8 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2) ^ 2) ^ 3 := by ring
          _ = (1 / 2 : ℝ) ^ 3 := by rw [h3]
          _ = (1 / 8 : ℝ) := by norm_num
      have h5 : (Real.sqrt 2 / 2 : ℝ) ^ 6 + (Real.sqrt 2 / 2 : ℝ) ^ 6 = (1 / 4 : ℝ) := by
        rw [h4]
        norm_num
      norm_num [h5]
  · -- Show 4 is the greatest
    intro x hx
    rcases hx with ⟨α, hα, hx⟩
    rw [hA] at hx
    rcases hα with ⟨hα1, hα2⟩
    have h3 : sin α ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h4 : cos α ≥ 0 := by
      apply cos_nonneg_of_mem_Icc
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have h5 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h6 : sin α ^ 6 + cos α ^ 6 ≥ (1 / 4 : ℝ) := by
      have h7 : sin α ^ 2 + cos α ^ 2 = 1 := h5
      nlinarith [sq_nonneg (sin α ^ 2 - 1 / 2), sq_nonneg (cos α ^ 2 - 1 / 2),
        sq_nonneg (sin α ^ 2 - cos α ^ 2), pow_two_nonneg (sin α ^ 2 - 1 / 2), pow_two_nonneg (cos α ^ 2 - 1 / 2), sq_nonneg (sin α ^ 2), sq_nonneg (cos α ^ 2), h3, h4, mul_nonneg (show 0 ≤ sin α ^ 2 by positivity) (show 0 ≤ cos α ^ 2 by positivity)]
    have h7 : 1 / (sin α ^ 6 + cos α ^ 6) ≤ (4 : ℝ) := by
      have h8 : sin α ^ 6 + cos α ^ 6 ≥ (1 / 4 : ℝ) := h6
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [h8]
    have hx_eq : 1 / (sin α ^ 6 + cos α ^ 6) = x := by 
      simpa using hx
    have h8 : x ≤ (4 : ℝ) := by
      have h9 : 1 / (sin α ^ 6 + cos α ^ 6) = x := by 
        linarith [hx_eq]
      have h10 : (1 / (sin α ^ 6 + cos α ^ 6) : ℝ) ≤ (4 : ℝ) := h7
      have h11 : sin α ^ 6 + cos α ^ 6 > 0 := by nlinarith [h3, h4, h5, h6]
      nlinarith [h9, h10, h11]
    linarith [h8]