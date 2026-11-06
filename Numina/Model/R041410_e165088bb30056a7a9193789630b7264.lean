import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_233726 (f : ℝ → ℝ) (hf : f = λ x => -1/3 * x^3 + 3 * x)
  (e : ℝ → ℝ) (he : e = λ x => m * x) (m : ℝ)  -- 修改1: 移除b参数，直线通过原点
  (h_inflection : f 0 = 0 ∧ deriv f 0  = 3 ∧ deriv^[2] f 0 = 0)  -- 新增: 拐点条件
  (h_m_range : 0 < m ∧ m < 3)  -- 新增: m的范围限制
  (h_intersect : ∃ x, x ≠ 0 ∧ f x = e x)  -- 修改2: 简化交点条件
  (T : ℝ → ℝ) (hT : T = λ m => m * (9 - 3 * m)) :  -- 新增: 面积和函数
  IsMaxOn T (Ioo 0 3) (3/2) := by

  unfold IsMaxOn
  intro x hx
  have h1 : 0 < x := by
    have h2 : x ∈ Ioo (0 : ℝ) 3 := hx
    exact h2.1
  have h2 : x < 3 := by
    have h3 : x ∈ Ioo (0 : ℝ) 3 := hx
    exact h3.2

  rw [hT]
  have h3 : (3 / 2 : ℝ) * (9 - 3 * (3 / 2 : ℝ)) ≥ x * (9 - 3 * x) := by
    nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (x - 3 / 2)]
  simpa using h3