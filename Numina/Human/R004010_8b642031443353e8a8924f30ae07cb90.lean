import Mathlib

open Real Filter Finset
open scoped Topology

-- Assume that the function f is continuous on [0, 1].
-- Show that (∑ i ∈ range n, f (i / n)) / n converges to ∫ x in (0)..1, f x as n goes to infinity.
lemma sum_tendsto_integral_of_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => (∑ i ∈ range n, f (i / n)) / n) atTop (𝓝 (∫ x in (0)..1, f x)) := by
  -- It is enough to show that for any e > 0, there exists N such that
  -- |(∑ i ∈ range n, f (i / n)) / n - ∫ x in (0)..1, f x| < e for all n ≥ N.
  simp only [NormedAddCommGroup.tendsto_atTop, norm_eq_abs]
  intro e he
  -- f is uniformly continuous on [0, 1] (because [0, 1] is compact).
  have hu : UniformContinuousOn f (Set.Icc 0 1) := IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hf
  simp [Metric.uniformContinuousOn_iff, dist_eq_norm] at hu
  -- We can find d > 0 such that |x - y| < d implies |f x - f y| < e / 2 for all x, y ∈ [0, 1].
  have ⟨d, hd, h⟩ := hu (e / 2) (by linarith)
  -- Choose N such that N > 1 / d.
  have ⟨N, hN⟩ := exists_nat_gt (1 / d)
  use N
  intro n hn
  have hn0 : 0 < n := by
    rify at hn ⊢
    apply lt_of_lt_of_le _ hn
    apply lt_trans _ hN
    positivity
  -- f is continuous on [i / n, (i + 1) / n] for all i < n.
  have hfc {i} (hi : i < n) : ContinuousOn f (Set.Icc (i / n) ((i + 1) / n)) := by
    apply hf.mono
    apply Set.Icc_subset_Icc
    · apply div_nonneg (by positivity) (by positivity)
    · rw [div_le_one] <;> norm_cast
  calc
    -- Rewrite the goal as
    -- |∑ i ∈ range n, (f (i / n) / n - ∫ x in (i / n)..((i + 1) / n), f x)| < e.
    _ = |∑ i ∈ range n, (f (i / n) / n - ∫ x in (i / n)..((i + 1) / n), f x)| := by
      rw [sum_sub_distrib, sum_div]
      congr
      simp_rw [show ∀ i : ℕ, (i + 1 : ℝ) = (i + 1 : ℕ) by simp]
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      · field_simp
      · intro k hk
        apply ContinuousOn.intervalIntegrable_of_Icc
        · gcongr
          linarith
        · push_cast
          exact hfc hk
    -- We have (f (i / n) / n - ∫ x in (i / n)..((i + 1) / n), f x)
    --     = ∫ x in (i / n)..((i + 1) / n), f (i / n) - f x.
    _ = |∑ i ∈ range n, ∫ x in (i / n)..((i + 1) / n), f (i / n) - f x| := by
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_sub]
      · congr
        rw [intervalIntegral.integral_const]
        simp [show (i + 1 : ℝ) / n - (i / n) = 1 / n by field_simp]
        ring
      · apply intervalIntegrable_const
      · apply ContinuousOn.intervalIntegrable_of_Icc
        · gcongr
          linarith
        · simp only [mem_range] at hi
          exact hfc hi
    -- The absolute value of the sum is less or equal then the sum of absolute values.
    _ ≤ ∑ i ∈ range n, |∫ x in (i / n)..((i + 1) / n), f (i / n) - f x| := by
      apply abs_sum_le_sum_abs
    -- Show that |∫ x in (i / n)..((i + 1) / n), f (i / n) - f x| ≤ (e / 2) / n.
    _ ≤ ∑ i ∈ range n, (e / 2) / n := by
      gcongr with i hi
      simp only [mem_range] at hi
      have eq : (e / 2) / n = (e / 2) * |(i + 1 : ℝ) / n - i / n| := by
        field_simp [abs_of_nonneg]
      rw [eq, ← norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      -- It is enough to show that |f (i / n) - f x| ≤ e / 2 for all x ∈ (i / n, (i + 1) / n].
      rw [Set.uIoc_of_le (by gcongr; linarith)]
      simp only [Set.mem_Ioc, norm_eq_abs, and_imp]
      intro x hx1 hx2
      apply le_of_lt
      apply h
      · positivity
      · rify at hi hn0
        rw [div_le_iff₀] <;> linarith
      · apply le_trans _ (le_of_lt hx1)
        positivity
      · apply le_trans hx2
        rw [div_le_iff₀] <;> norm_cast; linarith
      -- Show that |i / n - x| < d.
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      suffices 1 / n < d by
        apply lt_of_le_of_lt _ this
        rw [sub_le_iff_le_add]
        field_simp [add_comm]
        exact hx2
      rw [div_lt_iff₀ (by norm_cast)]
      rw [div_lt_iff₀ hd] at hN
      apply lt_of_lt_of_le hN
      rw [mul_comm]
      gcongr
    -- ∑ i ∈ range n, e / 2 / n = e / 2 < e.
    _ < e := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      field_simp
      rw [div_lt_iff₀ (by positivity)]
      rify at hn0
      nlinarith

-- Prove that ∫ x in (0)..1, √(1 - x^2) = π / 4.
lemma integral_sqrt_one_sub_sq' : ∫ x in (0)..1, √(1 - x^2) = π / 4 := by
  -- Mathlib already has the following integral:
  -- ∫ x in (-1)..1, √(1 - x^2) = π / 2.
  -- So it is enough to show that ∫ x in (-1)..0, √(1 - x^2) = ∫ x in (0)..1, √(1 - x^2).
  have heq : ∫ x in (-1)..0, √(1 - x^2) = ∫ x in (0)..1, √(1 - x^2) := calc
    _ = ∫ x in (0 - 1)..(0 - 0), √(1 - x^2) := by simp
    _ = ∫ x in (0)..1, √(1 - x^2) := by
      rw [← intervalIntegral.integral_comp_sub_left]
      simp only [zero_sub, even_two, Even.neg_pow]
  symm
  calc
    _ = (1 / 2) * ∫ x in (-1)..1, √(1 - x^2) := by
      rw [integral_sqrt_one_sub_sq]
      ring
    _ = (1 / 2) * ((∫ x in (-1)..0, √(1 - x^2)) + ∫ x in (0)..1, √(1 - x^2)) := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      all_goals {
        apply Continuous.intervalIntegrable
        fun_prop
      }
    _ = ∫ x in (0)..1, √(1 - x^2) := by
      rw [heq]
      ring

/- 29.50. Calculate the limit $\lim _{n \rightarrow \infty} \sum_{k=0}^{n-1} \frac{\sqrt{n^{2}-k^{2}}}{n^{2}}$. -/
theorem calculus_230040 :
    Tendsto (λ n => ∑ k in range n, sqrt (n^2 - k^2) / n^2) atTop (𝓝 (Real.pi / 4)) := by
  -- Define f(x) = √(1 - x^2).
  set f : ℝ → ℝ := fun x => √(1 - x ^ 2)
  -- f is continuous on [0, 1].
  have hf : ContinuousOn f (Set.Icc 0 1) := by fun_prop
  -- Use sum_tendsto_integral_of_continuous to show that the sum converges to
  -- the integral of f.
  convert sum_tendsto_integral_of_continuous hf with n
  -- Show that ∑ k ∈ range n, √(n^2 - k^2) / n^2 = (∑ k ∈ range n, f (k / n)) / n.
  · by_cases hn0 : n = 0
    -- If n = 0 then the result is trivial.
    · simp [hn0]
    -- If n ≠ 0 then √(n^2 - k^2) / n^2 = √(n^2 / n^2 - k^2 / n^2) / n = √(1 - (k / n)^2) / n.
    simp_rw [sum_div, f]
    apply sum_congr rfl
    intro k hk
    field_simp [pow_two]
  -- Use integral_sqrt_one_sub_sq' to finish the proof.
  · rw [integral_sqrt_one_sub_sq']