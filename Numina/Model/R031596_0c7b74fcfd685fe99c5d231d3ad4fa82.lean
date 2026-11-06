import Mathlib

open Real

theorem calculus_155952 (f : ℝ → ℝ) (hf : f = fun x => (x^2 + 2 * x) ^ ((1 : ℝ) / 3)) (x0 : ℝ) (hx0 : x0 = 2) (h : Differentiable ℝ f) :
    deriv f x0 * (2.004 - x0) + f x0 = 2.002 := by
  rw [hx0]
  have h1 : f 2 = (2 ^ 2 + 2 * (2 : ℝ)) ^ ((1 : ℝ) / 3) := by
    rw [hf]
  have h2 : f 2 = (2 : ℝ) := by
    rw [h1]
    have h3 : (2 ^ 2 + 2 * (2 : ℝ)) = (8 : ℝ) := by norm_num
    rw [h3]
    have h4 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
      have h5 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h5]
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    linarith [h4]
  have hf' : deriv f 2 = (1 / 2 : ℝ) := by
    rw [hf]
    have h3 : deriv (fun (x : ℝ) => (x ^ 2 + 2 * x) ^ ((1 : ℝ) / 3)) (2 : ℝ) = (8 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) := by
      simp [deriv_pow, deriv_add, deriv_mul, deriv_id'', mul_comm]
      all_goals norm_num
      <;> ring_nf <;> norm_num
      all_goals ring_nf <;> norm_num
      all_goals norm_num
      <;> ring_nf <;> norm_num
    have h4 : (8 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) = (1 / 2 : ℝ) := by
      have h5 : (8 : ℝ) ^ (-(2 / 3 : ℝ)) = (1 / 4 : ℝ) := by
        have h8 : (8 : ℝ) ^ (-(2 / 3 : ℝ)) = ((2 : ℝ) ^ (3 : ℝ)) ^ (-(2 / 3 : ℝ)) := by norm_num
        rw [h8]
        rw [← Real.rpow_mul]
        norm_num
        norm_num
        all_goals norm_num
        <;> ring_nf <;> norm_num
        all_goals try linarith
        all_goals try tauto
      rw [h5]
      norm_num
    rw [h3]
    linarith [h4]
    all_goals norm_num
    <;> ring_nf <;> norm_num
    all_goals try linarith
    all_goals try tauto
  rw [hf']
  rw [h2]
  all_goals norm_num
  all_goals try linarith
  all_goals try tauto
  <;> norm_num
  all_goals try tauto
  all_goals try tauto