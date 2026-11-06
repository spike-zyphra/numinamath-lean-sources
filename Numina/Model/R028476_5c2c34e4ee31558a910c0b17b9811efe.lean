import Mathlib

open Finset Real Complex Polynomial

theorem algebra_281401 {a : ℕ → ℂ}
    (ha : ∀ n, a n = ∏ i ∈ Icc 1 n, (1 + I / sqrt i)) :
    ∀ n, ‖a n - a (n + 1)‖ = 1 := by 
  intro n
  have eq1 : a (n + 1) = a n * (1 + I / sqrt (n + 1 : ℝ)) := by 
    rw [ha (n + 1), ha n]
    rw [prod_Icc_succ_top (by linarith)]
    all_goals simp
  have h2 : ‖a n - a (n + 1)‖ = ‖a n‖ * (1 / sqrt (n + 1 : ℝ)) := by
    rw [eq1]
    have h3 : a n - (a n * (1 + I / sqrt (n + 1 : ℝ))) = a n * (-I / sqrt (n + 1 : ℝ)) := by 
      field_simp [Complex.ext_iff, Complex.I_mul_I]
      <;> ring 
    rw [h3]
    have h4 : ‖a n * (-I / sqrt (n + 1 : ℝ))‖ = ‖a n‖ * ‖(-I / sqrt (n + 1 : ℝ))‖ := by 
      simpa using norm_mul (a n) (-I / sqrt (n + 1 : ℝ))
    rw [h4]
    have h5 : ‖(-I / sqrt (n + 1 : ℝ))‖ = (1 / sqrt (n + 1 : ℝ)) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    rw [h5]
  have h3 : ‖a n‖ = sqrt (n + 1 : ℝ) := by
    have h4 : ∀ (n : ℕ), ‖a n‖ = sqrt (n + 1 : ℝ) := by 
      intro n 
      induction n with 
      | zero =>
        rw [ha 0]
        simp [prod_eq_zero]
        <;> norm_num [Real.sqrt_one]
      | succ n ih =>
        have eq2 : a (n + 1) = a n * (1 + I / sqrt (n + 1 : ℝ)) := by 
          rw [ha (n + 1), ha n]
          rw [prod_Icc_succ_top (by linarith)]
          all_goals simp 
        have h5 : ‖a (n + 1)‖ = ‖a n‖ * ‖(1 + I / sqrt (n + 1 : ℝ))‖ := by 
          rw [eq2]
          simpa using norm_mul (a n) (1 + I / sqrt (n + 1 : ℝ))
        have h51 : ‖(1 + I / sqrt (n + 1 : ℝ))‖ = Real.sqrt (1 + 1 / (n + 1 : ℝ)) := by 
          have h1 : ‖(1 + I / sqrt (n + 1 : ℝ))‖ = Real.sqrt (1 + (1 / sqrt (n + 1 : ℝ)) ^ 2) := by 
            simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
            <;> ring_nf
          rw [h1]
          have h2 : (1 + (1 / sqrt (n + 1 : ℝ)) ^ 2) = (1 + 1 / (n + 1 : ℝ)) := by 
            have h1a : (1 / sqrt (n + 1 : ℝ) ) ^ 2 = 1 / (n + 1 : ℝ) := by 
              have hsqrt : sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
              field_simp [hsqrt]
            rw [h1a]
          rw [h2]
        rw [h5, ih, h51]
        have h7 : sqrt (n + 1 : ℝ) * Real.sqrt (1 + 1 / (n + 1 : ℝ)) = Real.sqrt ((n + 2 : ℝ)) := by
          have h8 : sqrt (n + 1 : ℝ) * Real.sqrt (1 + 1 / (n + 1 : ℝ)) = Real.sqrt (( (n + 1 : ℝ) ) * (1 + 1 / (n + 1 : ℝ)) ) := by 
            rw [← Real.sqrt_mul (by positivity)]
          rw [h8]
          have h9 : ( (n + 1 : ℝ) ) * (1 + 1 / (n + 1 : ℝ) ) = (n + 2 : ℝ) := by 
            field_simp 
            <;> ring 
          rw [h9]
        exact_mod_cast h7 
    specialize h4 n 
    simpa using h4 
  rw [h2, h3]
  field_simp [Real.sqrt_pos.2 (show (0 : ℝ) < (n + 1 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity)]