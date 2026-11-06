import Mathlib

open Real Set
open scoped Real

theorem algebra_196693 (A : ℝ → ℝ)
  (hA : A = λ α => 1 / (sin α ^ 4 + cos α ^ 4)) :
  IsGreatest {x | ∃ α ∈ Icc 0 (π/2), A α = x} 2 := by
  constructor
  · -- Show 2 is in the set
    use Real.pi / 4
    constructor
    · -- Show that π/4 is in the interval.
      constructor
      · -- Show 0 ≤ π/4.
        linarith [Real.pi_pos]
      · -- Show π/4 ≤ π/2.
        linarith [Real.pi_pos]
    · -- Show that A(π/4) = 2.
      rw [hA]
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact sin_pi_div_four
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        exact cos_pi_div_four
      simp [h1, h2]
      have h3 : Real.sqrt 2 ^ 2 = 2 := by
        exact Real.sq_sqrt (by linarith)
      field_simp [h3]
      <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h3, sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
  · -- Show 2 is the greatest element.
    intro x hx
    rcases hx with ⟨α, hα, hx⟩
    rw [hA] at hx
    rcases hα with ⟨h1, h2⟩
    have h5 : sin α ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h6 : cos α ≥ 0 := by
      apply cos_nonneg_of_neg_pi_div_two_le_of_le
      all_goals
      linarith [Real.pi_pos]
    have h7 : sin α ^ 4 + cos α ^ 4 ≥ 1 / 2 := by
      have h8 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      have h9 : sin α ^ 4 + cos α ^ 4 = (sin α ^ 2 + cos α ^ 2)^2 - 2 * (sin α * cos α)^2 := by 
        ring
      rw [h9, h8]
      have h10 : 0 ≤ 2 * (sin α * cos α)^2 := by positivity
      have h11 : sin α * cos α = (1 / 2) * sin (2 * α) := by
        rw [sin_two_mul]
        <;> ring_nf 
      have h12 : 2 * (sin α * cos α)^2 = (1 / 2) * sin (2 * α)^2 := by
        rw [h11]
        ring_nf
      have h13 : sin (2 * α) ^ 2 ≤ 1 := sin_sq_le_one (2 * α)
      linarith [h12, h13]
    have h8 : 1 / (sin α ^ 4 + cos α ^ 4) ≤ 2 := by
      have h9 : sin α ^ 4 + cos α ^ 4 ≥ 1 / 2 := h7
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have hx_eq_div : x = 1 / (sin α ^ 4 + cos α ^ 4) := by
      have hA' : (λ α => 1 / (sin α ^ 4 + cos α ^ 4)) α = x := by
        simpa using hx
      have h_eq : 1 / (sin α ^ 4 + cos α ^ 4) = x := by
        simpa using hA'
      linarith [h_eq]
    linarith [h8, hx_eq_div]