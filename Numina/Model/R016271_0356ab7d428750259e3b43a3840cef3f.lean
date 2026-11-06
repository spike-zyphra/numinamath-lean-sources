import Mathlib

open Real Set
open scoped Real

theorem algebra_174680 {f : ℝ → ℝ} (hf : f = λ x => sqrt ((1 - x) / (1 + x)))
  (α : ℝ) (hα : α ∈ Ioo (π/2) π) :
  f (cos α) + f (-cos α) = 2 / sin α := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : f (cos α) = sqrt ((1 - cos α) / (1 + cos α)) := by rw [hf]
  have h5 : f (-cos α) = sqrt ((1 - (-cos α) ) / (1 + (-cos α) ) ) := by rw [hf]
  have h6 : f (-cos α) = sqrt ((1 + cos α) / (1 - cos α) ) := by
    rw [h5]
    ring_nf
  rw [h4, h6]
  have h7 : 1 + cos α > 0 := by
    have h8 : cos α > -1 := by
      have h9 : α < π := by linarith [h2, Real.pi_pos]
      have h10 : cos α > cos π := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [h1, h2, Real.pi_pos]
      have h11 : cos π = -1 := by 
        exact Real.cos_pi
      linarith [h11, h10]
    linarith
  have h8 : 1 - cos α > 0 := by
    have h9 : cos α < 1 := by
      have h10 : cos α < cos (0 : ℝ) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [h1, h2, Real.pi_pos]
      have h11 : cos (0 : ℝ) = 1 := by 
        exact Real.cos_zero
      linarith [h11, h10]
    linarith
  have h9 : sqrt ((1 - cos α) / (1 + cos α) ) = Real.sqrt (1 - cos α) / Real.sqrt (1 + cos α) := by 
    rw [Real.sqrt_div (by linarith)]
  have h10 : sqrt ((1 + cos α) / (1 - cos α) ) = Real.sqrt (1 + cos α) / Real.sqrt (1 - cos α) := by 
    rw [Real.sqrt_div (by linarith)]
  rw [h9, h10]
  have h11' : Real.sqrt (1 - cos α) ^ 2 = 1 - cos α := by
    rw [Real.sq_sqrt]
    linarith
  have h12' : Real.sqrt (1 + cos α) ^ 2 = 1 + cos α := by
    rw [Real.sq_sqrt]
    linarith
  have h13'' : Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) = sin α := by
    have h14'' : (Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) ) ^ 2 = sin α ^ 2 := by
      calc
        (Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) ) ^ 2
          = (Real.sqrt (1 + cos α) ) ^ 2 * (Real.sqrt (1 - cos α) ) ^ 2 := by ring 
        _ = (1 + cos α) * (1 - cos α) := by rw [h11', h12']
        _ = 1 - cos α ^ 2 := by ring_nf
        _ = sin α ^ 2 := by 
          have h17 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
          linarith
    have h15'' : 0 ≤ Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) := by positivity
    have h16'' : Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) = Real.sqrt ( (Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) ) ^ 2 ) := by
      rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) by positivity)]
    have h17 : Real.sqrt ( (Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) ) ^ 2 ) = Real.sqrt (sin α ^ 2) := by 
      rw [h14'']
    have h18 : Real.sqrt (sin α ^ 2) = sin α := by
      rw [Real.sqrt_sq (show 0 ≤ sin α by linarith)]
    have h19 : Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) = sin α := by
      linarith [h16'', h17, h18]
    linarith
  have h19' : Real.sqrt (1 - cos α) ^ 2 + Real.sqrt (1 + cos α) ^ 2 = 2 := by
    nlinarith [h11', h12']
  have h20' : Real.sqrt (1 - cos α) / Real.sqrt (1 + cos α) + Real.sqrt (1 + cos α) / Real.sqrt (1 - cos α) = (Real.sqrt (1 - cos α) ^ 2 + Real.sqrt (1 + cos α) ^ 2) / (Real.sqrt (1 + cos α) * Real.sqrt (1 - cos α) ) := by 
    field_simp [show Real.sqrt (1 + cos α) ≠ 0 by positivity, show Real.sqrt (1 - cos α) ≠ 0 by positivity]
    <;> nlinarith
  rw [h20']
  rw [h13'', h19']