import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_305992 (f : ℝ → ℝ) (a b c : ℝ)
  (hf : ∀ x ∈ Icc 0 1, |f x| ≤ 1) (h : f = λ x => a * x ^ 2 + b * x + c) :
  |a| + |b| + |c| ≤ 17 := by
  have h1 := hf 0 (by norm_num)
  simp [h] at h1
  have h2 := hf 1 (by norm_num)
  simp [h] at h2
  have h3 := hf (1 / 2) (by norm_num)
  simp [h] at h3
  have h4 := hf (2 / 3) (by norm_num)
  simp [h] at h4
  have h5 := hf (1 / 3) (by norm_num)
  simp [h] at h5
  cases' abs_le.mp h1 with h11 h12
  cases' abs_le.mp h2 with h21 h22
  cases' abs_le.mp h3 with h31 h32
  cases' abs_le.mp h4 with h41 h42
  cases' abs_le.mp h5 with h51 h52
  cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> cases' abs_cases c with hc hc <;> 
    all_goals
      linarith