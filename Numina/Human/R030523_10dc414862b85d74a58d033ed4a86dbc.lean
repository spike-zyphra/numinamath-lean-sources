import Mathlib

open Topology Filter Real

/- Example 6. Find $\lim _{x \rightarrow+\infty} x\left(\operatorname{arctg} x-\frac{\pi}{2}\right)$. -/
theorem calculus_161675 :
    Tendsto (λ x => x * (Real.arctan x - Real.pi / 2)) atTop (𝓝 (-1)) := by
  -- Let f(x) = tan(x) * (x - π / 2).
  set f := fun x => tan x * (x - π / 2)
  -- It is enough to prove that lim f = -1 as x tends to π / 2 from left.
  suffices hf : Tendsto f (𝓝[<] (π / 2)) (𝓝 (-1)) by
    -- We have x * (arctan(x) - π / 2) = f (arctan (x))
    rw [show (fun x => x * (arctan x - π / 2)) = f ∘ arctan by ext x; simp [f]]
    -- We have lim arctan = π / 2 as x tends to infinity, so lim (f ∘ arctan) = lim f as x tends to π / 2 from left.
    exact Tendsto.comp hf tendsto_arctan_atTop
  -- Rewrite f as follows:
  -- f(x) = tan(x) * (x - π / 2) = sin(x) / cos(x) * (x - π / 2) = sin(x) * (x - π / 2) / sin(π / 2 - x).
  simp_rw [f, tan_eq_sin_div_cos, ← sin_pi_div_two_sub, div_mul_eq_mul_div]
  -- Apply L'Hôpital's rule to h(x) / g(x) with h(x) = sin(x) * (x - π / 2) and g(x) = sin(π / 2 - x).
  apply HasDerivAt.lhopital_zero_left_on_Ioo (show 0 < π / 2 by positivity)
          (f' := fun x => cos x * (x - π / 2) + sin x) (g' := fun x => -cos (π / 2 - x))
  -- Show that the derivative of sin(x) * (x - π / 2) is cos(x) * (x - π / 2) + sin(x).
  · intro x hx
    rw [← mul_one (sin x)]
    apply HasDerivAt.mul (hasDerivAt_sin x)
    apply HasDerivAt.sub_const
    exact hasDerivAt_id' x
  -- Show that the derivative of sin(π / 2 - x) is -cos(π / 2 - x).
  · intro x hx
    rw [neg_eq_neg_one_mul, mul_comm (-1)]
    apply HasDerivAt.sin
    apply HasDerivAt.const_sub
    exact hasDerivAt_id' x
  -- Show that -cos(π / 2 - x) ≠ 0 for x ∈ (0, π / 2).
  · simp only [Set.mem_Ioo, ne_eq, neg_eq_zero, and_imp]
    intro x hx1 hx2
    rw [cos_pi_div_two_sub]
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi hx1 (by linarith)
  -- Show that lim (sin(x) * (x - π / 2)) = 0 as x tends to π / 2.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show 0 = sin (π / 2) * (π / 2 - π / 2) by simp]
    -- The result follows from continuity of sin(x) * (x - π / 2).
    apply Continuous.tendsto
    fun_prop
  -- Show that lim (sin(π / 2 - x)) = 0 as x tends to π / 2.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show 0 = sin (π / 2 - π / 2) by simp]
    -- The result follows from continuity of sin(π / 2 - x).
    apply Continuous.tendsto
    fun_prop
  -- It is left to show that lim h'(x) / g'(x) = lim (cos(x) * (x - π / 2) + sin(x)) / (-cos(π / 2 - x)) = -1
  -- as x tends to π / 2.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show (-1 : ℝ) = (cos (π / 2) * (π / 2 - π / 2) + sin (π / 2)) / -cos (π / 2 - π / 2) by simp]
    apply Tendsto.div _ _ (by norm_num)
    -- Show that lim (cos(x) * (x - π / 2) + sin(x)) = 1 as x tends to π / 2.
    -- The result follows from continuity of this function.
    · apply Continuous.tendsto
      fun_prop
    -- Show that lim (-cos(π / 2 - x)) = -1 as x tends to π / 2.
    -- The result follows from continuity of this function.
    · apply Continuous.tendsto
      fun_prop