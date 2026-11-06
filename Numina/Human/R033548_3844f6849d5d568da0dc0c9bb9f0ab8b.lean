import Mathlib

open Topology Filter Real

/- ## Problem Statement

Calculate the limit of the function:

$\lim _{x \rightarrow a}\left(2-\frac{x}{a}\right)^{\tan\left(\frac{\pi x}{2 a}\right)}$ -/
theorem calculus_137220 {a : ℝ} (ha : a ≠ 0) :
    Tendsto (λ x => (2 - x / a) ^ tan (π * x / (2 * a))) (𝓝[≠] a) (𝓝 (exp (2 / π))) := by
  -- Prove a result missing in Mathlib:
  -- the derivative of cot(x) is -1 / sin(x)^2 when sin(x) ≠ 0.
  have hasDerivAt_cot x (hx : sin x ≠ 0) : HasDerivAt cot (-1 / sin x ^ 2) x := by
    simp_rw [show cot = (fun x => cos x / sin x) by ext x; rw [cot_eq_cos_div_sin]]
    have eq : -1 / sin x^2 = ((-sin x) * sin x - cos x * cos x) / sin x^2 := by
      rw [show -sin x * sin x - cos x * cos x = -(cos x^2 + sin x^2) by ring]
      rw [cos_sq_add_sin_sq]
    rw [eq]
    exact HasDerivAt.div (hasDerivAt_cos x) (hasDerivAt_sin x) hx
  -- We have 0 < |a| since a ≠ 0.
  have ha1 : 0 < |a| := abs_pos.mpr ha
  -- Define an auxiliary set s = (a - |a| / 2, a + |a| / 2) \ {a}.
  -- set s : Set ℝ := Set.Ioo (-2 * |a|) (2 * |a|) \ {0, a}
  set s : Set ℝ := Set.Ioo (a - |a| / 2) (a + |a| / 2) \ {a}
  -- Show that s ∈ 𝓝[≠] a.
  have hs : s ∈ 𝓝[≠] a := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by linarith) (by linarith)
  -- Prove an auxiliary inequality: |x| < 3 / 2 * |a| for x ∈ s.
  have hsa {x} (hx : x ∈ s) : |x| < 3 / 2 * |a| := by
    simp only [neg_mul, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    rw [abs_lt]
    constructor
    · linarith [neg_abs_le a]
    · linarith [le_abs_self a]
  -- Show that x ∈ s implies that x ≠ 0.
  have hsx {x} (hx : x ∈ s) : x ≠ 0 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    by_cases h : a < 0
    · rw [abs_of_neg h] at hx
      linarith
    · simp at h
      rw [abs_of_nonneg h] at hx
      linarith
  -- Show that 0 < 2 - x / a for x ∈ s.
  have hs1 {x} (hx : x ∈ s) : 0 < 2 - x / a := by
    rw [sub_pos]
    calc
      x / a ≤ |x / a| := le_abs_self _
      _ = |x| / |a| := by rw [abs_div]
      _ < 3 / 2 * |a| / |a| := by
        gcongr
        exact hsa hx
      _ < 2 := by
        rw [mul_div_cancel_right₀ _ (by positivity)]
        norm_num
  -- Show that sin (π * x / (2 * a)) ≠ 0 for x ∈ s.
  have hs2 {x} (hx : x ∈ s) : sin (π * x / (2 * a)) ≠ 0 := by
    -- We have |π * x / (2 * a)| < π (since |x| < 3 / 2 * |a| for x ∈ s).
    have ineq : |π * x / (2 * a)| < π := calc
      |π * x / (2 * a)| = (π / 2) * (|x| / |a|) := by
        simp_rw [abs_div, abs_mul, abs_of_pos pi_pos]
        norm_num
        ring
      _ < (π / 2) * (3 / 2 * |a| / |a|) := by
        gcongr
        exact hsa hx
      _ < π := by
        rw [mul_div_cancel_right₀ _ (by positivity)]
        linarith [pi_pos]
    contrapose! hsx
    rw [abs_lt] at ineq
    -- Suppose that sin (π * x / (2 * a)) = 0.
    -- Then π * x / (2 * a) = 0 (since |π * x / (2 * a)| < π).
    rw [sin_eq_zero_iff_of_lt_of_lt ineq.1 ineq.2] at hsx
    rw [show π * x / (2 * a) = (π / (2 * a)) * x by ring, mul_eq_zero] at hsx
    -- π / (2 * a) ≠ 0, so x = 0, a contradiction (x ≠ 0 for x ∈ s).
    have : π / (2 * a) ≠ 0 := by positivity
    simp [this] at hsx
    use x
  have eq1 : π * a / (2 * a) = π / 2 := by field_simp; ring
  -- We have
  -- (2 - x / a)^tan(π * x / (2 * a)) = exp(log(2 - x / a) / cot(π * x / (2 * a)))
  -- for all x ∈ s.
  have eq : exp ∘ (fun x => (log (2 - x / a) / cot (π * x / (2 * a)))) =ᶠ[𝓝[≠] a] (fun x => (2 - x / a) ^ tan (π * x / (2 * a))) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use s, hs
    intro x hx
    simp [rpow_def_of_pos (hs1 hx), cot_eq_cos_div_sin, tan_eq_sin_div_cos, ← div_mul]
    ring_nf
  -- It is enough to show that
  -- lim exp(log(2 - x / a) / cot(π * x / (2 * a))) = exp(2 / π) when x tends to a.
  apply Tendsto.congr' eq
  clear eq
  -- exp is continuous so it is enough to show that
  -- lim log(2 - x / a) / cot(π * x / (2 * a)) = 2 / π as x tends to a.
  apply Tendsto.comp (y := 𝓝 (2 / π)) (Continuous.tendsto continuous_exp _)
  -- Apply L'Hôpital's rule.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => -(a⁻¹ * 1) / (2 - x / a)) (g' := fun x => (-1 / sin (π * x / (2 * a)) ^ 2 * (π / (2 * a) * 1)))
  -- Show that the derivative of log(2 - x / a) is -a⁻¹ / (2 - x / a) for all x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.log
    · apply HasDerivAt.const_sub
      simp_rw [show ∀ x, x / a = a⁻¹ * x by intros; ring]
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
    · exact ne_of_gt (hs1 hx)
  -- Show that the derivative of cot(π * x / (2 * a)) is
  -- (-1 / sin (π * x / (2 * a)) ^ 2 * (π / (2 * a)) for all x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply HasDerivAt.comp (h₂ := cot) x
    · apply hasDerivAt_cot
      exact hs2 hx
    · simp_rw [show ∀ x, π * x / (2 * a) = π / (2 * a) * x by intros; ring]
      apply HasDerivAt.const_mul
      exact hasDerivAt_id' x
  -- Show that (-1 / sin (π * x / (2 * a)) ^ 2 * (π / (2 * a)) ≠ 0 for all x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    have := hs2 hx
    positivity
  -- Show that lim log(2 - x / a) = 0 as x tends to a.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show 0 = log (2 - a / a) by field_simp [ha]; norm_num]
    apply ContinuousAt.tendsto
    have : 2 - a / a = 1 := by field_simp [ha]; norm_num
    fun_prop (disch := linarith)
  -- Show that lim cot(π * x / (2 * a)) = 0 as x tends to a.
  · simp_rw [cot_eq_cos_div_sin]
    have eq : 0 = cos (π * a / (2 * a)) / sin (π * a / (2 * a)) := by simp [eq1]
    rw [eq]
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Tendsto.div  _ _ (by simp [eq1]) <;> apply ContinuousAt.tendsto <;> fun_prop
  -- It is left to show that
  -- lim (-(a⁻¹ * 1) / (2 - x / a)) / ((-1 / sin (π * x / (2 * a)) ^ 2 * (π / (2 * a) * 1)) = 2 / π
  -- as x tends to a.
  -- This function is continuous at x = a so the result follows from
  -- 2 / π = -(a⁻¹ * 1) / (2 - a / a) / (-1 / sin (π * a / (2 * a))^2 * (π / (2 * a) * 1)).
  have eq : 2 / π = -(a⁻¹ * 1) / (2 - a / a) / (-1 / sin (π * a / (2 * a))^2 * (π / (2 * a) * 1)) := by
    field_simp [eq1]
    ring
  rw [eq]
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  apply ContinuousAt.tendsto
  have : 2 - a / a = 1 := by field_simp [ha]; norm_num
  apply ContinuousAt.div (by fun_prop (disch := linarith)) _ (by simp [eq1, pi_ne_zero, ha])
  apply ContinuousAt.mul _ (by fun_prop)
  apply ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [eq1])