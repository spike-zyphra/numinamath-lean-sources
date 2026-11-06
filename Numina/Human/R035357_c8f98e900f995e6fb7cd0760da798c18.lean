import Mathlib
open Polynomial
/- Let $f(x)$ be the polynomial \[f(x)=3x^4+5x^2-9x-2.\] If $g(x)$ is equal to the polynomial $f(x-1)$, what is the sum of the coefficients of $g$? -/
theorem algebra_21959 {f g : Polynomial ℝ} (hf : f = 3 * X ^ 4 + 5 * X ^ 2 - 9 * X - 2)
    (hg : g = f.comp (X - 1)) : ∑ i in Finset.Icc 0 g.natDegree, g.coeff i = -2 := by
    simp [hf] at hg -- 将 f 代入 hg
    ring_nf at hg -- 化简 hg
    have hg0 : g.coeff 0 = 15 := by -- 计算 g 的第 0 项
      simp [hg]
    have hg1 : g.coeff 1 = -31 := by -- 计算 g 的第 1 项
      simp [hg]
    have hg2 : g.coeff 2 = 23 := by -- 计算 g 的第 2 项
      simp [hg]
      have H : (X : ℝ[X]).coeff 2 = 0 := coeff_X_of_ne_one (by simp) -- 计算 X 的第 2 项
      simp [H]
    have hg3 : g.coeff 3 = -12 := by -- 计算 g 的第 3 项
      simp [hg]
      have H : (X : ℝ[X]).coeff 3 = 0 := coeff_X_of_ne_one (by simp)
      simp [H]
    have hg4 : g.coeff 4 = 3 := by -- 计算 g 的第 4 项
      simp [hg]
      have H : (X : ℝ[X]).coeff 4 = 0 := coeff_X_of_ne_one (by simp)
      simp [H]
    have degg : g.natDegree = 4 := by -- 计算 g 的次数
      rw [hg]
      compute_degree!
    simp [degg, Finset.Icc, LocallyFiniteOrder.finsetIcc, List.range'] -- 计算 g 的系数和
    linarith