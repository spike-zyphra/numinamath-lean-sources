import Mathlib

theorem algebra_163479 {b c : ℝ} (P : ℝ → ℝ) (hP : ∀ x, P x = x ^ 2 + b * x + c)
    (hP1 : P (P 1) = 0) (hP2 : P (P 2) = 0) (hP3 : P 1 ≠ P 2) :
    P 0 = -3 / 2 := by 
  have h1 : P 1 = 1 + b + c := by
    rw [hP 1]
    ring
  have h2 : P 2 = 4 + 2 * b + c := by
    rw [hP 2]
    ring
  have eq1 : P (P 1) = (P 1) ^ 2 + b * (P 1) + c := by
    apply hP
  have eq2 : P (P 2) = (P 2) ^ 2 + b * (P 2) + c := by
    apply hP
  have hP1' : (P 1) ^ 2 + b * (P 1) + c = 0 := by 
    rw [eq1] at hP1 
    linarith 
  have hP2' : (P 2) ^ 2 + b * (P 2) + c = 0 := by 
    rw [eq2] at hP2 
    linarith 
  have eq3 : (P 1 - P 2) * (P 1 + P 2 + b) = 0 := by
    nlinarith [hP1', hP2']
  have hneq : P 1 - P 2 ≠ 0 := by
    intro h 
    apply hP3
    linarith 
  have eq4 : P 1 + P 2 + b = 0 := by 
    apply (mul_left_inj' hneq).mp 
    linarith [eq3] 
  have h0 : P 0 = c := by
    rw [hP 0]
    ring
  rw [h1] at eq4 hP1' 
  rw [h2] at hP2' 
  nlinarith [hP1', hP2', eq4, h0]