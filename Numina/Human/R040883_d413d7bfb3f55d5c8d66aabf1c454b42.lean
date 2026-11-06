import Mathlib

open Real Set
open scoped Topology

/- 11. (20 points) Let $\alpha, \beta$ be any two interior angles of a triangle. If there exist $\alpha, \beta$ such that the inequality

$$

\cos \sqrt{\alpha} + \cos \sqrt{\beta} > a + \cos \sqrt{\alpha \beta}

$$


holds, find the range of real number $a$. -/
theorem inequalities_244444 (a : ℝ) :
    (∃ α β : ℝ, α ∈ Ioo 0 π ∧ β ∈ Ioo 0 π ∧ α + β < π ∧
    cos √α + cos √β > a + cos √(α * β)) ↔ a < 1 := by
  constructor
  -- Show that x ∈ [0, π] ∧ β ∈ [0, π] ∧ α + β < π ∧ cos √x + cos √y > a + cos √(x * y)
  -- implies that a < 1.
  · intro ⟨x, y, hx, hy, hxy, h⟩
    simp only [mem_Ioo] at hx hy
    -- Let z = (√x + √y) / 2.
    set z := (√x + √y) / 2
    -- Define f(t) = 1 + cos (t * t) - 2 * cos t.
    set f : ℝ → ℝ := fun t => 1 + cos (t * t) - 2 * cos t
    -- Show that 0 < z (from 0 < x and 0 < y).
    have hz0 : 0 < z := by
      suffices 0 < √x ∧ 0 < √y by dsimp [z]; linarith
      simp_rw [sqrt_pos]
      exact ⟨hx.1, hy.1⟩
    -- Show that z < √(π / 2).
    have hz : z < √(π / 2) := by
      -- It is enough to show that z^2 ≤ π / 2.
      rw [← sq_lt_sq₀ (le_of_lt hz0) (by positivity), sq_sqrt (by positivity)]
      calc
        -- We have z^2 = (√x + √y)^2 / 4
        --       ≤ 2 * (√x ^ 2 + √y ^ 2) / 4 (because (a + b)^2 ≤ 2 * (a^2 + b^2) for all a and b)
        --       = (x + y) / 2 < π / 2 (because x + y < π).
        z ^ 2 = (√x + √y) ^ 2 / 4 := by field_simp [z]; norm_num
        _ ≤ 2 * (√x ^ 2 + √y ^ 2) / 4 := by gcongr; exact add_sq_le
        _ = (x + y) / 2 := by
            rw [sq_sqrt (le_of_lt hx.1), sq_sqrt (le_of_lt hy.1)]
            ring
        _ < π / 2 := by linarith
    -- Prove an auxiliary inequality √(π / 2) ≤ π / 2.
    have hpi2 : √(π / 2) ≤ π / 2 := by
      -- It is enough to show that π / 2 ≤ (π / 2) ^ 2
      rw [Real.sqrt_le_left (by positivity)]
      -- The inequality follows from π / 2 ≤ 1.4 ^ 2 and 1.4 ≤ π / 2.
      trans 1.4 ^ 2
      · linarith [Real.pi_lt_d2]
      · apply pow_le_pow_left₀ (by norm_num)
        linarith [Real.pi_gt_d2]
    -- Prove an auxiliary inequality: x ∈ [0, √(π / 2)] implies x * x ≤ π / 2.
    have hpi2_sq {x} (hx0 : 0 ≤ x) (hx : x ≤ √(π / 2)) : x * x ≤ π / 2 := by
      rw [show π / 2 = √(π / 2) * √(π / 2) by rw [← pow_two, sq_sqrt (by positivity)]]
      gcongr
    -- Show that cos √x + cos √y ≤ 2 * cos z
    have hineq1 : cos √x + cos √y ≤ 2 * cos z := calc
      -- We have cos √x + cos √y = 2 * cos z * cos ((√x - √y) / 2)
      --                         ≤ 2 * cos z * 1
      -- (from cos ((√x - √y) / 2) ≤ 1 and 0 ≤ 2 * cos z)
      --                         = 2 * cos z.
      cos √x + cos √y = 2 * cos z * cos ((√x - √y) / 2) := by rw [cos_add_cos]
      --
      _ ≤ 2 * cos z * 1 := by
          gcongr
          · apply mul_nonneg (by norm_num)
            apply Real.cos_nonneg_of_mem_Icc
            simp only [mem_Icc]
            constructor <;> linarith
          · exact cos_le_one _
      _ = 2 * cos z := by rw [mul_one]
    -- Show that cos (z * z) ≤ cos (√x * √y).
    have hineq2 : cos (z * z) ≤ cos (√x * √y) := by
      have h_pi : π = √π * √π := by rw [← pow_two, sq_sqrt (by positivity)]
      -- cos is decreasing on [0, π].
      -- So it is enough to show that √x * √y ∈ [0, π], z * z ∈ [0, π], and √x * √y ≤ z * z.
      apply strictAntiOn_cos.antitoneOn
      · simp only [mem_Icc]
        -- We have 0 ≤ √x * √y ≤ π because 0 < x < π and 0 < y < π.
        refine ⟨by positivity, ?_⟩
        rw [h_pi]
        gcongr <;> linarith
      · simp only [mem_Icc]
        -- We have 0 ≤ z * z ≤ π because 0 < z and z < √(π / 2) ≤ π / 2 < π.
        refine ⟨by positivity, ?_⟩
        linarith [hpi2_sq (le_of_lt hz0) (le_of_lt hz)]
      · calc
          -- √x * √y = (4 * √x * √y) / 4
          --         ≤ (√x + √y)^2 / 4 (because 4 * a * b ≤ (a + b)^2 for all a and b)
          --         = z * z.
          √x * √y = (4 * √x * √y) / 4 := by ring
          _ ≤ (√x + √y)^2 / 2^2 := by
              gcongr
              exact four_mul_le_pow_two_add √x √y
              norm_num
          _ = z * z := by ring
    -- Prove that 0 < f(t) for all t ∈ (0, √(π / 2)).
    have hf_pos {t} (ht : t ∈ Ioo 0 √(π / 2)) : 0 < f t := by
      simp only [mem_Ioo] at ht
      have ht2 : t ∈ Icc 0 π := by
        simp only [mem_Icc, le_of_lt ht.1, true_and]
        linarith
      -- Consider two cases: t ∈ (0, 1] and t ∈ [1, √(π / 2)).
      by_cases ht1 : t ≤ 1
      · calc
          -- If t ≤ 1 then we have 1 - cos(t) > 0 and cos(t * t) ≥ cos(t)
          -- (because t * t ≤ t when t ∈ (0, 1]).
          -- So we get f(t) = (1 - cos(t)) + (cos(t * t) - cos(t)) > 0.
          0 = 0 + 0 := by rw [add_zero]
          _ < (1 - cos t) + (cos (t * t) - cos t) := by
            apply add_lt_add_of_lt_of_le
            · rw [sub_pos, ← Real.cos_zero]
              apply strictAntiOn_cos (by simp; linarith) ht2 (by linarith)
            · rw [sub_nonneg]
              apply strictAntiOn_cos.antitoneOn _ ht2
              · suffices 0 ≤ (1 - t) * t by linear_combination this
                apply mul_nonneg (by linarith) (le_of_lt ht.1)
              · simp only [mem_Icc, ←pow_two, pow_two_nonneg, true_and]
                rw [pow_two]
                linarith [hpi2_sq (le_of_lt ht.1) (le_of_lt ht.2)]
          _ = f t := by ring
      -- Now assume that t ≥ 1.
      push_neg at ht1
      -- Show that 0 < f(√(π / 2)).
      have h0 : 0 < f √(π / 2) := by
        simp only [← pow_two, sub_pos, f]
        -- cos(π / 2) = 0 so we get the following inequality:
        -- 2 * cos(√(π / 2)) < 1.
        rw [sq_sqrt (by positivity), cos_pi_div_two]
        -- It is enough to prove that cos √(π / 2) < cos(π / 3) (since cos(π / 3) = 1 / 2).
        suffices cos √(π / 2) < cos (π / 3) by
          rw [cos_pi_div_three] at this
          linear_combination 2 * this
        -- cos is strictly decreasing on [0, π] so we need to show that π / 3 < √(π / 2).
        apply strictAntiOn_cos
        · simp only [mem_Icc]
          constructor <;> linarith
        · simp only [mem_Icc]
          constructor <;> linarith
        · apply Real.lt_sqrt_of_sq_lt
          -- We have (π / 3) ^ 2 < 1.2 ^ 2 < π / 2 so π / 3 < √(π / 2).
          trans 1.2 ^ 2
          · apply pow_lt_pow_left₀ (by linarith [pi_lt_d2]) (by positivity) (by norm_num)
          · linarith [pi_gt_d2]
      apply lt_of_lt_of_le h0
      -- We have 0 < f(√(π / 2)). Show that f(√(π / 2)) ≤ f(t) for t ∈ (1, √(π / 2)] by
      -- showing that f'(t) ≤ 0 on this interval.
      apply antitoneOn_of_deriv_nonpos (convex_Ioc 1 √(π / 2)) (by fun_prop) (by fun_prop) _ _ _ (by linarith)
      -- Show that f'(x) ≤ 0.
      · simp only [interior_Ioc, mem_Ioo, and_imp]
        intro x hx1 hx2
        unfold f
        -- Compute the derivative of f:
        -- f'(x) = 2 * (sin(x) - x * sin(x^2)).
        rw [deriv_sub (by fun_prop) (by fun_prop), deriv_const_add, deriv_const_mul _ (by fun_prop), Real.deriv_cos]
        rw [_root_.deriv_cos (by fun_prop), deriv_mul (by fun_prop) (by fun_prop)]
        simp
        -- Show that sin(x) ≤ x * sin(x^2) for x ∈ (1, √(π / 2)].
        -- It is enough to show that 0 ≤ sin(x) ≤ sin(x^2).
        suffices 1 * sin x ≤ x * sin (x * x) by linarith
        gcongr
        -- 0 ≤ sin(x) because t ∈ (1, √(π / 2)) ⊆ [0, π].
        · apply sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        -- sin is increasing on [-π / 2, π / 2] so we need to show that x ≤ π / 2, x * x ≤ π / 2,
        -- and x ≤ x * x.
        · apply strictMonoOn_sin.monotoneOn
          · simp only [mem_Icc]
            constructor <;> linarith
          · simp only [mem_Icc]
            constructor
            · rw [← pow_two]
              linarith [pow_two_nonneg x]
            · exact hpi2_sq (by linarith) (le_of_lt hx2)
          -- x ≤ x * x because 1 < x.
          · suffices 0 ≤ x * (x - 1) by linear_combination this
            exact mul_nonneg (by linarith) (by linarith)
      -- Show that t ∈ (1, √(π / 2)].
      · simp only [mem_Ioc]
        constructor <;> linarith
      -- Show that √(π / 2) ∈ (1, √(π / 2)].
      · simp only [mem_Ioc]
        refine ⟨?_, by linarith⟩
        rw [← sqrt_one]
        apply sqrt_lt_sqrt zero_le_one
        linarith
    -- We have cos √x + cos √y > a + cos √(x * y).
    -- So the inequality a < 1 follows from 1 + cos √(x * y) - (cos √x + cos √y) > 0.
    suffices 1 + cos √(x * y) - (cos √x + cos √y) > 0  by linarith
    -- We have 1 + cos √(x * y) - (cos √x + cos √y)
    --          ≥ 1 + cos (z * z) - 2 * cos z (from hineq1 and hineq2)
    --          = f(z)
    --          > 0 (because z ∈ (0, √(π / 2))).
    calc
      _ ≥ 1 + cos (z * z) - 2 * cos z := by
          rw [sqrt_mul]
          gcongr
          exact le_of_lt hx.1
      _ = f z := by rfl
      _ > 0 := by
          apply hf_pos
          simp only [mem_Ioo]
          exact ⟨hz0, hz⟩
  -- Suppose now that a < 1 and show that there exist x and y such that
  -- cos √x + cos √y > a + cos √(x * y)
  · intro ha
    -- The limit of g(x) = cos √x + cos √x - cos √(x * x) is 1 as x tends to 0 (x > 0).
    have : Filter.Tendsto (fun x => cos √x + cos √x - cos √(x * x)) (𝓝[>] 0) (𝓝 1) := by
      apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      rw [show 1 = cos √0 + cos √0 - cos √(0 * 0) by simp]
      -- The function g(x) is continuous so the limit is equal to g(0) = 1.
      apply Continuous.tendsto
      fun_prop
    -- (a, 2) is an open neighborhood of 1.
    have hs : Ioo a 2 ∈ 𝓝 1 := by
      apply IsOpen.mem_nhds isOpen_Ioo
      simp only [mem_Ioo, Nat.one_lt_ofNat, and_true]
      exact ha
    have := Filter.Tendsto.eventually_mem this hs
    -- lim g(x) = 1 as x tends to 0 (x > 0), so there exists u such that 0 < u and
    -- g(x) ∈ (a, 2) for x in (0, u).
    simp only [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset, mem_Ioi] at this
    have ⟨u, hu, h⟩ := this
    -- Let x = min(u / 2, π / 4)
    set x := (u / 2) ⊓ (π / 4)
    -- 0 < x.
    have hx0 : 0 < x := by positivity
    -- x ≤ π / 4 < π / 2.
    have hx1 : x < π / 2 := by
      simp [x]
      right
      linarith [pi_pos]
    -- Let y = x.
    use x, x
    -- We have x ∈ (0, π), x + x < π.
    simp [mem_Ioo, gt_iff_lt, and_self_left, hx0, (show x < π by linarith), (show x + x < π by linarith)]
    -- 0 < x ≤ u / 2 < u, so g(x) ∈ (a, 2).
    have hx : x ∈ {x | cos √x + cos √x - cos √(x * x) ∈ Ioo a 2} := by
      apply Set.mem_of_subset_of_mem h
      simp [hx0, x]
      exact Or.inl hu
    -- g(x) ∈ (a, 2) implies cos √x + cos √x - cos √(x * x) > a.
    simp only [mem_Ioo, mem_setOf_eq] at hx
    linarith