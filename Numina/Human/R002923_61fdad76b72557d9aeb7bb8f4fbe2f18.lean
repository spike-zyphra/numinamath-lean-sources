import Mathlib

open Real Filter
open scoped Topology

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow \frac{1}{2}} \frac{\ln (4 x-1)}{\sqrt{1-\cos \pi x}-1}$ -/
theorem calculus_130853 (f : ℝ → ℝ)
    (hf : f = λ x => log (4 * x - 1) / (sqrt (1 - cos (π * x)) - 1)) :
    Tendsto f (𝓝[≠] (1 / 2)) (𝓝 (8 / π)) := by
  have heq : π * (1 / 2) = π / 2 := by ring
  -- Let s = (1/4, 3/4) \ {1/2}.
  set s : Set ℝ := Set.Ioo (1 / 4) (3 / 4) \ {1 / 2}
  -- Show taht s ∈ 𝓝[≠] (1 / 2).
  have hs : s ∈ 𝓝[≠] (1 / 2) := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by norm_num) (by norm_num)
  -- We have 4 * x - 1 ≠ 0 for all x ∈ s.
  have hs1 {x} (hx : x ∈ s) : 4 * x - 1 ≠ 0 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    linarith
  -- We have 1 - cos (π * x) ≠ 0 for all x ∈ s.
  have hs2 {x} (hx : x ∈ s) : 1 - cos (π * x) ≠ 0 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    suffices ¬ cos (π * x) = 1 by contrapose! this; linarith
    rw [cos_eq_one_iff_of_lt_of_lt (by nlinarith [pi_pos]) (by nlinarith [pi_pos])]
    nlinarith [pi_pos]
  -- We have sin (π * x) ≠ 0 for all x ∈ s.
  have hs3 {x} (hx : x ∈ s) : sin (π * x) ≠ 0 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos]) (by nlinarith [pi_pos])
  rw [hf]
  -- Apply L'Hôpital's rule.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => 4 / (4 * x - 1)) (g' := fun x => π * sin (π * x) / (2 * √(1 - cos (π * x))))
  · -- Show that the derivative of log (4 * x - 1) is 4 / (4 * x - 1)
    -- for all x ∈ s.
    rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.log _ (by apply hs1 hx)
    apply HasDerivAt.sub_const
    nth_rw 2 [show (4 : ℝ) = 4 * 1 by norm_num]
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  · -- Show that the derivative of √(1 - cos (π * x)) - 1 is
    -- π * sin (π * x) / (2 * √(1 - cos (π * x))) for all x ∈ s.
    rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.sub_const
    apply HasDerivAt.sqrt _ (by apply hs2 hx)
    rw [show π * sin (π * x) = -(-sin (π * x) * (π * 1)) by ring]
    apply HasDerivAt.const_sub
    apply HasDerivAt.cos
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  · -- Show that π * sin (π * x) / (2 * √(1 - cos (π * x))) ≠ 0
    -- for all x ∈ s.
    rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    have := hs3 hx
    apply div_ne_zero (by positivity)
    apply mul_ne_zero (by norm_num)
    apply (sqrt_ne_zero _).mpr (hs2 hx)
    simp only [sub_nonneg]
    exact cos_le_one (π * x)
  · -- Show that lim (log (4 * x - 1)) = 0 as x → 1 / 2.
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show (0 : ℝ) = log (4 * (1 / 2) - 1) by norm_num]
    apply ContinuousAt.tendsto
    fun_prop (disch := norm_num)
  · -- Show that lim (√(1 - cos (π * x)) - 1) = 0 as x → 1 / 2.
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show 0 = √(1 - cos (π * (1 / 2))) - 1 by rw [heq]; simp]
    apply ContinuousAt.tendsto
    fun_prop
  -- We have 8 / π = 4 / (4 * (1 / 2) - 1) / (π * sin (π * (1 / 2)) / (2 * √(1 - cos (π * (1 / 2))))).
  have eq : 8 / π = 4 / (4 * (1 / 2) - 1) / (π * sin (π * (1 / 2)) / (2 * √(1 - cos (π * (1 / 2))))) := by
    rw [heq]
    simp
    ring
  rw [eq]
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  apply ContinuousAt.tendsto
  -- It is left to show that
  -- 4 / (4 * x - 1) / (π * sin (π * x) / (2 * (√(1 - cos(π * x)))))
  -- is continuous at x = 1/2.
  apply ContinuousAt.div (by fun_prop (disch := norm_num))
  · apply ContinuousAt.div (by fun_prop) (by fun_prop)
    rw [heq]
    simp
  · rw [heq]
    simp
    linarith [pi_pos]