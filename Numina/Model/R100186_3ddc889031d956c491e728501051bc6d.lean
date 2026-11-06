import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_270679 {f : ℝ → ℝ} (hf : f = λ x => 1/2 + logb 2 (x/(1-x)))
  (A B : ℝ × ℝ) (hA : A.1 ∈ Ioo 0 1) (hB : B.1 ∈ Ioo 0 1)
  (hAB : A.2 = f A.1 ∧ B.2 = f B.1) (hM : (A.1 + B.1)/2 = 1/2) :
  (A.2 + B.2)/2 = 1/2 := by
  have h1 : A.1 + B.1 = 1 := by 
    linarith
  have h2 : A.2 = f A.1 := hAB.left
  have h3 : B.2 = f B.1 := hAB.right
  rw [h2, h3, hf]
  have h4 : 0 < A.1 := hA.left
  have h5 : A.1 < 1 := hA.right
  have h6 : 0 < B.1 := by
    have hB1 : B.1 ∈ Ioo 0 1 := hB
    exact hB1.left
  have h7 : B.1 < 1 := by
    have hB1 : B.1 ∈ Ioo 0 1 := hB
    exact hB1.right
  have h8 : B.1 = 1 - A.1 := by
    linarith
  simp [h8]
  have h9 : logb 2 (A.1 / (1 - A.1)) + logb 2 ((1 - A.1) / A.1) = 0 := by
    have h10 : logb 2 (A.1 / (1 - A.1)) = logb 2 (A.1) - logb 2 (1 - A.1) := by
      rw [logb_div (by linarith) (by linarith)]
    have h11 : logb 2 ((1 - A.1) / A.1) = logb 2 (1 - A.1) - logb 2 (A.1) := by
      rw [logb_div (by linarith) (by linarith)]
    rw [h10, h11]
    ring
  linarith [h9]