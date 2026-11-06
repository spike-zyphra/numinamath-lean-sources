import Mathlib

open Real

theorem inequalities_81222 : (∑ i ∈ Finset.range 2015, (1 / (sqrt (i + 1) + sqrt (i + 2)))) ^ 2 * (2017 + 24 * sqrt 14) = 2015 ^ 2 := by 
  have h1 : ∀ i : ℕ, 1 / (sqrt (i + 1) + sqrt (i + 2)) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by 
      positivity
    have h3 : (i + 1 : ℝ) ≥ 0 := by positivity
    have h4 : (i + 2 : ℝ) ≥ 0 := by positivity
    -- Multiply numerator and denominator by the conjugate
    field_simp [h2]
    <;> ring_nf <;> rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    <;> ring_nf <;> norm_num
    <;> ring
  have h2 : ∑ i ∈ Finset.range 2015, (1 / (sqrt (i + 1) + sqrt (i + 2))) = sqrt 2016 - 1 := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (sqrt (i + 2) - sqrt (i + 1)) = sqrt (n + 1) - 1 := by 
      intro n
      induction n with 
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        <;> ring_nf <;> simp [Real.sqrt_sq]
        <;> ring_nf <;> norm_num
        <;> ring
    specialize h3 2015
    norm_num at h3 ⊢
    exact h3
  rw [h2]
  have h3 : sqrt 2016 = 12 * sqrt 14 := by 
    calc 
      sqrt 2016 = sqrt (12^2 * 14) := by norm_num
      _ = sqrt (12^2) * sqrt 14 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (12 : ℝ) * sqrt 14 := by rw [Real.sqrt_sq (by norm_num)]
      _ = 12 * sqrt 14 := by ring
  rw [h3]
  nlinarith [Real.sq_sqrt (show (14 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 14]