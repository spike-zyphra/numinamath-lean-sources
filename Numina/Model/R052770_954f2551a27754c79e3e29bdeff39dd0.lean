import Mathlib

theorem algebra_319699 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ 1)
    (h : f = fun x => a * x ^ 2 + b * x + c) :
    |a| + |b| + |c| ≤ 3 := by
  have h1 := hf 0 (by norm_num)
  simp [h] at h1
  have h2 := hf 1 (by norm_num)
  simp [h] at h2
  have h3 := hf (-1) (by norm_num)
  simp [h] at h3
  cases' abs_cases a <;> cases' abs_cases b <;> cases' abs_cases c <;> 
    linarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, sq_nonneg (a - b), sq_nonneg (a + b)]