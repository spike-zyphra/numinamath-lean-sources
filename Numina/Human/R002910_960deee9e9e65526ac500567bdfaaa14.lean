import Mathlib

open Topology Filter Real

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow 0}\left(\frac{\arcsin ^{2} x}{\arcsin ^{2} 4 x}\right)^{2 x+1}$ -/
theorem calculus_129004 :
    Tendsto (fun x => (arcsin x ^ 2 / arcsin (4 * x) ^ 2)^(2 * x + 1)) (𝓝[≠] 0) (𝓝 (1/16)) := by
  -- We have (arcsin x ^ 2 / arcsin (4 * x) ^ 2)^(2 * x + 1) = ((arcsin x / arcsin (4 * x))^2)^(2 * x + 1).
  have eq1 : (fun x => (arcsin x ^ 2 / arcsin (4 * x) ^ 2)^(2 * x + 1)) = (fun x => ((arcsin x / arcsin (4 * x))^2)^(2 * x + 1)) := by
    ext x
    rw [← div_pow]
  -- 1/16 = ((1/4)^2)^(2 * 0 + 1).
  rw [eq1, show (1 / 16 : ℝ) = ((1 / 4 : ℝ) ^ 2) ^ (2 * 0 + 1 : ℝ) by norm_num]
  -- It is enough to show that lim (2 * x + 1) = 1 and lim (arcsin x / arcsin (4 * x)) = 1/4.
  apply Tendsto.rpow
  rotate_left
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Continuous.tendsto
    fun_prop
  · norm_num
  apply Tendsto.pow
  -- Define s = (-1/4, 1/4) \ {0}.
  set s := Set.Ioo (-1 / 4 : ℝ) (1 / 4) \ {0}
  -- We have s ∈ 𝓝[≠] 0.
  have hs : s ∈ 𝓝[≠] 0 := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by norm_num) (by norm_num)
  -- Use L'Hôpital's rule to compute the limit of arcsin(x) / arcsin(4 * x) as x tends to 0.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => 1 / √(1 - x ^ 2)) (g' := fun x => 1 / √(1 - (4 * x)^2) * (4 * 1))
  · apply eventually_iff_exists_mem.mpr
    -- Show that the derivative of arcsin(x) is 1 / √(1 - x^2) inside s.
    use s, hs
    simp only [s, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
    intro x hx1 hx2 hx0
    apply hasDerivAt_arcsin (by linarith) (by linarith)
  · apply eventually_iff_exists_mem.mpr
    -- Show that the derivative of arcsin(4 * x) is 4 / √(1 - (4 * x)^2) inside s.
    use s, hs
    simp only [s, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
    intro x hx1 hx2 hx0
    rw [show (fun x => arcsin (4 * x)) = Real.arcsin ∘ (fun x => 4 * x) by ext x; rfl]
    apply HasDerivAt.comp
    · apply hasDerivAt_arcsin (by linarith) (by linarith)
    · apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
  · apply eventually_iff_exists_mem.mpr
    -- Show that 4 / √(1 - (4 * x)^2) ≠ 0 for x ∈ s.
    use s, hs
    simp only [s, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
    intro x hx1 hx2 hx0
    apply ne_of_gt
    apply mul_pos _ (by norm_num)
    apply div_pos zero_lt_one
    rw [sqrt_pos, sub_pos, show (1 : ℝ) = 1 ^ 2 by norm_num]
    rw [sq_lt_sq, show |(1 : ℝ)| = 1 by norm_num, abs_lt]
    constructor <;> linarith
  · nth_rw 3 [← arcsin_zero]
    -- Show that lim arcsin(x) = 0 as x tends to 0.
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply continuousAt_arcsin.tendsto
  . have eq : 0 = arcsin (4 * 0) := by simp
    -- Show that lim arcsin(4 * x) = 0 as x tends to 0.
    nth_rw 3 [eq]
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Continuous.tendsto
    rw [show (fun x => arcsin (4 * x)) = arcsin ∘ (fun x => 4 * x) by ext x; rfl]
    apply Continuous.comp _ (by fun_prop)
    exact continuous_arcsin
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    -- Show that lim (1 / √(1 - x^2)) / (4 / √(1 - (4 * x)^2)) = 1 / 4 as x tends to 0.
    rw [show (1 / 4 : ℝ) = 1 / √(1 - 0^2) / (1 / √(1 - (4 * 0)^2) * (4 * 1)) by simp]
    apply ContinuousAt.tendsto
    apply ContinuousAt.div _ _ (by simp)
    · apply ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
    · apply ContinuousAt.mul _ (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)