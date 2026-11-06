import Mathlib

open Real Set
open scoped Real

theorem algebra_196722 (f : ℝ → ℝ) (hf : f = λ α => sin α ^ 6 + cos α ^ 6)
  (I : Set ℝ) (hI : I = {α | α ∈ Icc 0 (π/2)}) :
  IsLeast {x | ∃ α ∈ I, f α = x} (1/4) := by
  constructor
  · -- Show 1/4 belongs to the image set
    use Real.pi / 4
    constructor
    · -- Show π/4 is in the set I
      rw [hI]
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that f(π/4) = 1/4
      rw [hf]
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      simp only [h1, h2]
      have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring
          _ = 2 / 4 := by rw [Real.sq_sqrt]; linarith
          _ = 1 / 2 := by norm_num
      have h4 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = (1 / 8 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2) ^ 2) ^ 3 := by ring
          _ = (1 / 2) ^ 3 := by rw [h3]
          _ = 1 / 8 := by norm_num
      linarith [h4]
  · -- Show 1/4 is the least
    intro x hx
    rcases hx with ⟨α, hα, hfx⟩
    rw [hI] at hα
    rcases hα with ⟨hα1, hα2⟩
    rw [hf] at hfx
    simp at hfx
    have h3 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    have h4 : sin α ^ 6 + cos α ^ 6 ≥ 1 / 4 := by
      have h6 : sin α ^ 6 + cos α ^ 6 = (sin α ^ 2 + cos α ^ 2) ^ 3 - 3 * (sin α ^ 2 * cos α ^ 2) * (sin α ^ 2 + cos α ^ 2) := by
        ring
      rw [h6, h3]
      have h7 : 0 ≤ sin α ^ 2 := by positivity
      have h8 : 0 ≤ cos α ^ 2 := by positivity
      have h9 : sin α ^ 2 * cos α ^ 2 ≥ 0 := by positivity
      nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α * cos α), Real.sin_sq_add_cos_sq α, Real.pi_pos]
    linarith [h4, hfx]