import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_221914 {a : ℝ} (ha : 0 < a) (A B P : ℝ × ℝ)
  (hA : A = (a, 0)) (hB : B = (0, a)) (hP : P ∈ segment ℝ A B)
  (hAP : ∃ t ∈ Icc 0 1, (P.1 - A.1) = t * (B.1 - A.1) ∧ (P.2 - A.2) = t * (B.2 - A.2)) :
  (A.1 * P.1 + A.2 * P.2) ≤ a ^ 2 := by
  rcases hAP with ⟨t, ht, h1, h2⟩
  have ht1 : 0 ≤ t := by 
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ht
    exact ht1.1
  have ht2 : t ≤ 1 := by 
    have ht2 : t ∈ Icc (0 : ℝ) 1 := ht
    exact ht2.2
  have eq1 : P.1 = a - a * t := by
    simp [hA, hB] at h1
    linarith
  have eq2 : P.2 = a * t := by
    simp [hA, hB] at h2
    linarith
  have h4 : a * P.1 + (0 : ℝ) * P.2 = a ^ 2 * (1 - t) := by 
    rw [eq1]
    ring
  have h3 : a ^ 2 * (1 - t) ≤ a ^ 2 := by 
    nlinarith [sq_nonneg (t), sq_nonneg (a), ht1, ht2, mul_pos ha (show 0 < 1 by norm_num)]
  simp [hA] at *
  nlinarith [h4, h3, mul_pos ha (show 0 < 1 by norm_num)]