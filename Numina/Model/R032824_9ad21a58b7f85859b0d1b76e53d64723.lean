import Mathlib

open Real

theorem inequalities_42516 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : (∑ i : Fin n, a i ^ 2) ≤ 1) (hb : (∑ i : Fin n, b i ^ 2) ≤ 1) :
    (1 - ∑ i : Fin n, a i ^ 2) * (1 - ∑ i : Fin n, b i ^ 2) ≤
    (1 - ∑ i : Fin n, a i * b i) ^ 2 := by
  have h1 : (∑ i : Fin n, a i ^ 2) ≤ 1 := ha
  have h2 : (∑ i : Fin n, b i ^ 2) ≤ 1 := hb
  have h3 : (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i : Fin n, a i ^ 2) * (∑ i : Fin n, b i ^ 2) := by 
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h4 : 0 ≤ (∑ i : Fin n, (a i - b i) ^ 2) := by 
    positivity
  have h5 : (∑ i : Fin n, (a i - b i) ^ 2) = (∑ i : Fin n, a i ^ 2) + (∑ i : Fin n, b i ^ 2) - 2 * (∑ i : Fin n, a i * b i) := by
    have eq1 : ∑ i : Fin n, (a i - b i) ^ 2 = ∑ i : Fin n, (a i ^ 2 + b i ^ 2 - 2 * (a i * b i)) := by 
      congr 
      funext i 
      ring_nf
    have eq2 : ∑ i : Fin n, (a i ^ 2 + b i ^ 2 - 2 * (a i * b i)) = (∑ i : Fin n, a i ^ 2) + (∑ i : Fin n, b i ^ 2) - 2 * (∑ i : Fin n, a i * b i) := by 
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      <;> ring 
    rw [eq1]
    all_goals 
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum] 
      <;> ring
  have h6 : (∑ i : Fin n, a i ^ 2) + (∑ i : Fin n, b i ^ 2) ≥ 2 * (∑ i : Fin n, a i * b i) := by 
    have h5p : (∑ i : Fin n, (a i - b i) ^ 2) ≥ 0 := h4
    linarith [h5p, h5]
  nlinarith [sq_nonneg (∑ i : Fin n, a i * b i - ((∑ i : Fin n, a i ^ 2) + (∑ i : Fin n, b i ^ 2)) / 2), 
      sq_nonneg ((∑ i : Fin n, a i ^ 2) - (∑ i : Fin n, b i ^ 2)), 
      sq_nonneg ( (∑ i : Fin n, a i) - (∑ i : Fin n, b i) ), 
      h3, h6, 
      mul_nonneg (show (0 : ℝ) ≤ 1 - (∑ i : Fin n, a i ^ 2) by linarith) 
          (show (0 : ℝ) ≤ 1 - (∑ i : Fin n, b i ^ 2) by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ (∑ i : Fin n, a i ^ 2) by positivity) 
          (show (0 : ℝ) ≤ (∑ i : Fin n, b i ^ 2) by positivity)
  ]