import Mathlib

open Topology Filter Real

/- ## Problem Statement
Calculate the limit of the function:
$$
\lim _{x \rightarrow 0}\left(\frac{1+x^{2} \cdot 2^{x}}{1+x^{2} \cdot 5^{x}}\right)^{\frac{1}{\sin ^{3} x}}
$$
 -/
theorem calculus_137670 :
    Tendsto (λ x => ((1 + x^2 * 2^x) / (1 + x^2 * 5^x)) ^ (1 / Real.sin x^3)) (𝓝[≠] 0) (𝓝 (2/5)) := by
  -- Prove an auxiliary lemma: if 0 < b then the derivative of b ^ x is b ^ x * log b.
  have hasDerivAt_const_rpow {b x : ℝ} (hb : 0 < b) : HasDerivAt (fun x => b ^ x) (b ^ x * log b) x := by
    simp_rw [rpow_def_of_pos hb]
    apply HasDerivAt.exp
    nth_rw 2 [show log b = log b * 1 by ring]
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  -- We have 2 ^ x is continuous at 0.
  have hc2 := continuousAt_const_rpow (show (2 : ℝ) ≠ 0 by norm_num) (b := 0)
  -- We have 5 ^ x is continuous at 0.
  have hc5 := continuousAt_const_rpow (show (5 : ℝ) ≠ 0 by norm_num) (b := 0)
  -- Define f b x = x^2 * b^x.
  set f : ℝ → ℝ → ℝ := fun b x => x ^ 2 * b ^ x
  -- Show that if 0 < b then f b is continuous.
  have hcf {b} (hb : 0 < b) : Continuous (f b) := by
    apply Continuous.mul (by fun_prop)
    rw [continuous_iff_continuousAt]
    intro x
    apply continuousAt_const_rpow
    linarith
  -- Show the if 0 < b then the derivative of f b is log b * f b x + 2 * x * b ^ x.
  have hdf {b x} (hb : 0 < b) : HasDerivAt (f b) (log b * f b x + 2 * x * b ^ x) x := by
    have : log b * f b x + 2 * x * b ^ x = 2 * x ^ 1 * b ^ x + x ^ 2 * (b ^ x * log b) := by ring
    rw [this]
    apply HasDerivAt.mul (hasDerivAt_pow _ _) (hasDerivAt_const_rpow hb)
  -- We have ((1 + x^2 * 2^x) / (1 + x^2 * 5^x)) ^ (1 / sin x^3)
  --   = exp ∘ (fun x => log ((1 + f 2 x) / (1 + f 5 x)) / sin x^3) for all x.
  have eq : (λ x => ((1 + x^2 * 2^x) / (1 + x^2 * 5^x)) ^ (1 / sin x^3)) = exp ∘ (fun x => log ((1 + f 2 x) / (1 + f 5 x)) / sin x^3) := by
    ext x
    rw [rpow_def_of_pos (by positivity)]
    field_simp
  rw [eq]
  -- It is enough to show that log ((1 + f 2 x) / (1 + f 5 x)) / sin x^3 tends to
  -- log (2 / 5) as x tends to 0 (since exp (log (2 / 5)) = 2 / 5 and exp is continuous).
  apply Tendsto.comp (y := 𝓝 (log (2 / 5)))
  · nth_rw 2 [show 2 / 5 = exp (log (2 / 5)) by rw [exp_log (by positivity)]]
    apply Continuous.tendsto continuous_exp
  -- Define s = (-1, 1) \ {0}.
  set s : Set ℝ := Set.Ioo (-1) 1 \ {0}
  -- We have s ∈ 𝓝[≠] 0.
  have hs : s ∈ 𝓝[≠] 0 := by
    unfold s
    rw [Set.diff_eq, Set.inter_comm]
    apply inter_mem_nhdsWithin
    apply Ioo_mem_nhds (by linarith) (by linarith)
  -- Show that sin x ≠ 0 for all x ∈ s.
  have hs1 {x} (hx : x ∈ s) : sin x ≠ 0 := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    have hx2 := hx.2
    contrapose! hx2
    rw [← sin_eq_zero_iff_of_lt_of_lt] <;> linarith [pi_lt_d4, pi_gt_d4]
  -- Show that 0 < cos x for all x ∈ s.
  have hs2 {x} (hx : x ∈ s) : 0 < cos x := by
    simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff, s] at hx
    apply cos_pos_of_le_one
    rw [abs_le]
    constructor <;> linarith
  -- Apply L'Hôpital's rule.
  apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => ((log 2 * f 2 x + 2 * x * 2 ^ x) * (1 + f 5 x) - (1 + f 2 x) * (log 5 * f 5 x + 2 * x * 5 ^ x)) / (1 + f 5 x)^2 / ((1 + f 2 x) / (1 + f 5 x))) (g' := fun x => 3 * sin x ^ 2 * cos x)
  -- Show that the derivative of log ((1 + f 2 x) / (1 + f 5 x)) is
  -- ((log 2 * f 2 x + 2 * x * 2 ^ x) * (1 + f 5 x) - (1 + f 2 x) * (log 5 * f 5 x + 2 * x * 5 ^ x)) / (1 + f 5 x)^2 / ((1 + f 2 x) / (1 + f 5 x)).
  · apply Eventually.of_forall
    intro x
    apply HasDerivAt.log _ (by positivity)
    apply HasDerivAt.div _ _ (by positivity)
    · apply HasDerivAt.const_add
      exact hdf (by norm_num)
    · apply HasDerivAt.const_add
      exact hdf (by norm_num)
  -- Show that the derivative of sin x ^ 3 is 3 * sin x ^ 2 * cos x.
  · apply Eventually.of_forall
    intro x
    apply HasDerivAt.pow
    apply hasDerivAt_sin
  -- Show that 3 * sin x^2 * cos x ≠ 0 for all x ∈ s.
  · rw [eventually_iff_exists_mem]
    use s, hs
    intro x hx
    apply ne_of_gt
    apply mul_pos _ (hs2 hx)
    have := hs1 hx
    positivity
  -- Show that lim (log ((1 + f 2 x) / (1 + f 5 x))) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = log ((1 + f 2 0) / (1 + f 5 0)) by simp [f]]
    -- It is enough to show that log ((1 + f 2 x) / (1 + f 5 x)) is continuous at 0.
    apply Continuous.tendsto
    apply Continuous.log _ (fun x => by positivity)
    apply Continuous.div _ _ (fun x => by positivity)
    · apply Continuous.add (by fun_prop) (hcf (by norm_num))
    · apply Continuous.add (by fun_prop) (hcf (by norm_num))
  -- Show that lim (sin x^3) = 0 as x tends to 0.
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 0 = sin 0 ^ 3 by simp]
    apply Continuous.tendsto
    fun_prop
  -- Rewrite the goal expression as:
  -- lim (2 * ((x / sin x) * (a(x) / sin x)) + (x / sin x)^2 * b(x)) / c(x) / d(x) / (3 * cos x) = log (2 / 5)
  -- where a, b, c, d are continuous at 0, c(0) ≠ 0, d(0) ≠ 0.
  replace eq x : (log 2 * f 2 x + 2 * x * 2 ^ x) * (1 + f 5 x) - (1 + f 2 x) * (log 5 * f 5 x + 2 * x * 5 ^ x)
      = 2 * x * (2 ^ x - 5 ^ x) + x ^ 2 * (log 2 * 2 ^ x * (1 + f 5 x) + 2 * x * 5 ^ x - log 5 * 5 ^ x * (1 + f 2 x) - 2 * x * 5 ^ x) := by
    ring
  simp_rw [eq]
  replace eq a b c d x : (2 * x * a + x ^ 2 * b) / c / d / (3 * sin x ^ 2 * cos x) = (2 * ((x / sin x) * (a / sin x)) + (x / sin x)^2 * b) / c / d / (3 * cos x) := by
    field_simp
    ring_nf
  simp_rw [eq]
  -- We have
  -- log (2 / 5) = (2 * (1 * (log 2 - log 5)) + 1 ^ 2 * (log 2 - log 5)) / (1 + f 5 0)^2 / ((1 + f 2 0) / (1 + f 5 0)) / (3 * cos 0).
  replace eq : log (2 / 5) = (2 * (1 * (log 2 - log 5)) + 1 ^ 2 * (log 2 - log 5)) / (1 + f 5 0)^2 / ((1 + f 2 0) / (1 + f 5 0)) / (3 * cos 0) := by
    simp [f, log_div]
    ring
  rw [eq]
  -- Apply basic properties of limits to the goal and get the following subgoals:
  -- lim (x / sin x) = 1 and lim ((2 ^ x - 5 ^ x) / sin x) = log 2 - log 5.
  apply Tendsto.div _ _ (by norm_num); rotate_left
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Continuous.tendsto
    fun_prop
  apply Tendsto.div _ _ (by norm_num); rotate_left
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    apply ContinuousAt.div _ _ (by positivity) <;> fun_prop (disch := simp)
  apply Tendsto.div _ _ (by norm_num); rotate_left
  · apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)
  -- Show that lim (x / sin x) = 1 as x tends to 0.
  have hsin : Tendsto (fun x => x / sin x) (𝓝[≠] 0) (𝓝 1) := by
    -- Apply L'Hôpital's rule.
    apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => 1) (g' := cos)
    -- Show that the derivative of x is 1.
    · apply Eventually.of_forall
      exact hasDerivAt_id'
    -- Show that the derivative of sin x is cos x.
    · apply Eventually.of_forall
      exact hasDerivAt_sin
    -- Show that cos x ≠ 0 for all x ∈ s.
    · rw [eventually_iff_exists_mem]
      use s, hs
      intro x hx
      exact ne_of_gt (hs2 hx)
    -- Show that lim x = 0 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply Continuous.tendsto (by fun_prop)
    -- Show that lim sin(x) = 0 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      nth_rw 2 [show 0 = sin 0 by simp]
      apply Continuous.tendsto (by fun_prop)
    -- Show that lim (1 / cos x) = 1 as x tends to 0.
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    nth_rw 2 [show 1 = 1 / cos 0 by simp]
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)
  apply Tendsto.add
  · apply Tendsto.const_mul
    apply Tendsto.mul hsin
    -- Show that lim (2 ^ x - 5 ^ x) / sin(x) = log 2 - log 5 as x tends to 0.
    -- Apply L'Hôpital's rule.
    apply HasDerivAt.lhopital_zero_nhds' (f' := fun x => 2 ^ x * log 2 - 5 ^ x * log 5) (g' := cos)
    -- Show that the derivative of 2 ^ x - 5 ^ x is 2 ^ x * log 2 - 5 ^ x * log 5.
    · apply Eventually.of_forall
      intro x
      apply HasDerivAt.sub <;> apply hasDerivAt_const_rpow <;> norm_num
    -- Show that the derivative of sin x is cos x.
    · apply Eventually.of_forall
      exact hasDerivAt_sin
    -- Show that cos x ≠ 0 for all x ∈ s.
    · rw [eventually_iff_exists_mem]
      use s, hs
      intro x hx
      exact ne_of_gt (hs2 hx)
    -- Show that lim(2 ^ x - 5 ^ x) = 0 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      nth_rw 2 [show (0 : ℝ) = 2 ^ (0 : ℝ) - 5 ^ (0 : ℝ) by simp]
      apply ContinuousAt.tendsto (by fun_prop)
    -- Show that lim sin(x) = 0 as x tends to 0.
    · apply Tendsto.mono_left _ nhdsWithin_le_nhds
      nth_rw 2 [show 0 = sin 0 by simp]
      apply Continuous.tendsto (by fun_prop)
    -- Show that lim (2^x * log 2 - 5^x * log 5) / cos(x) = log 2 - log 5 as x tends to 0.
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    rw [show log 2 - log 5 = (2 ^ (0 : ℝ) * log 2 - 5 ^ (0 : ℝ) * log 5) / cos 0 by simp]
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)
  · apply Tendsto.mul (Tendsto.pow hsin _)
    rw [show log 2 - log 5 = log 2 * 2 ^ (0 : ℝ) * (1 + f 5 0) + 2 * 0 * 5 ^ (0 : ℝ) - log 5 * 5 ^ (0 : ℝ) * (1 + f 2 0) - 2 * 0 * 5 ^ (0 : ℝ) by simp [f]]
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    fun_prop (disch := simp)