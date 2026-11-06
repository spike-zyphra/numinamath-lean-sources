import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_190117 {x y s t : ℝ} {n : ℕ} (h : x + I * y = (s + I * t) ^ n) :
    x ^ 2 + y ^ 2 = (s ^ 2 + t ^ 2) ^ n := by
  have eq3 : x = ((s + I * t) ^ n).re := by 
    have eq1 : (x + I * y).re = ((s + I * t) ^ n).re := by 
      exact congr_arg Complex.re h
    simp at eq1 ⊢
    linarith 
  have eq4 : y = ((s + I * t) ^ n).im := by 
    have eq1 : (x + I * y).im = ((s + I * t) ^ n).im := by 
      exact congr_arg Complex.im h 
    simp at eq1 ⊢
    linarith 
  have h3 : x^2 + y^2 = ((s + I * t)^n).re^2 + ((s + I * t)^n).im^2 := by
    rw [eq3, eq4]
    all_goals 
      simp [Complex.ext_iff] 
  have h4 : ((s + I * t) ^ n).re ^ 2 + ((s + I * t) ^ n).im ^ 2 = (s ^ 2 + t ^ 2) ^ n := by 
    have h5 : ((s + I * t) ^ n).re ^ 2 + ((s + I * t) ^ n).im ^ 2 = ((s + I * t) ^ n).normSq := by
      have h_eq : ((s + I * t) ^ n).normSq = ((s + I * t) ^ n).re ^ 2 + ((s + I * t) ^ n).im ^ 2 := by
        simp [Complex.normSq, pow_two]
      linarith [h_eq]
    rw [h5]
    have h6 : ((s + I * t) ^ n).normSq = (s ^ 2 + t ^ 2) ^ n := by 
      have h7 : ∀ k : ℕ, ((s + I * t) ^ k).normSq = (s ^ 2 + t ^ 2) ^ k := by 
        intro k 
        induction k with 
        | zero => 
          simp 
        | succ k ih => 
          simp [pow_succ, Complex.normSq] at ih ⊢
          norm_num at ih ⊢
          nlinarith [ih]
      specialize h7 n 
      simpa using h7 
    rw [h6] 
  rw [h3, h4]