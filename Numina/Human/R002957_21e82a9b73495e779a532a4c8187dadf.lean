import Mathlib

open Topology Filter

/- 6th Swedish 1966 Problem 1 Let {x} denote the fractional part of x = x - [x]. The sequences x 1 , x 2 , x 3 , ... and y 1 , y 2 , y 3 , ... are such that lim {x n } = lim {y n } = 0. Is it true that lim {x n + y n } = 0? lim {x n - y n } = 0? -/
theorem algebra_135234 :
    (∀ x y : ℕ → ℝ,
     Tendsto (λ n => x n - ⌊x n⌋) atTop (𝓝 0) →
     Tendsto (λ n => y n - ⌊y n⌋) atTop (𝓝 0) →
     Tendsto (λ n => (x n + y n) - ⌊(x n + y n)⌋) atTop (𝓝 0)) ∧
    ¬ (∀ x y : ℕ → ℝ,
     Tendsto (λ n => x n - ⌊x n⌋) atTop (𝓝 0) →
     Tendsto (λ n => y n - ⌊y n⌋) atTop (𝓝 0) →
     Tendsto (λ n => (x n - y n) - ⌊(x n - y n)⌋) atTop (𝓝 0)) := by
  constructor
  · -- Show that lim {x n} = 0 and lim {y n} = 0 imply that
    -- lim {x n + y n} = 0.
    intro x y hx hy
    simp only [Int.self_sub_floor, NormedAddCommGroup.tendsto_atTop, sub_zero,
      Real.norm_eq_abs] at hx hy ⊢
    intro e he
    -- We need to show that for any 0 < e, there exists N such that
    -- |{x n + y n}| < e for all n ≥ N.
    -- lim {x n} = 0 implies that there exists n1 such that
    -- |{x n}| < e / 2 for all n ≥ n1.
    have ⟨n1, h1⟩ := hx (e / 2) (by linarith)
    -- lim {y n} = 0 implies that there exists n2 such that
    -- |{y n}| < e / 2 for all n ≥ n2.
    have ⟨n2, h2⟩ := hy (e / 2) (by linarith)
    -- Let N = max n1 n2.
    use max n1 n2
    intro n hn
    -- We have |{u}| = {u} for all u.
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    calc
      -- We have {x + y} ≤ {x} + {y} for all x and y.
      Int.fract (x n + y n) ≤ Int.fract (x n) + Int.fract (y n) := by
        apply Int.fract_add_le
      -- {x} + {y} = |{x}| + |{y}|.
      _ = |Int.fract (x n)| + |Int.fract (y n)| := by
        repeat rw [abs_of_nonneg (Int.fract_nonneg _)]
      -- |{x n}| < e / 2 and |{y n}| < e / 2.
      _ < e / 2 + e / 2 := by
        gcongr
        · apply h1
          apply le_trans (Nat.le_max_left _ _) hn
        · apply h2
          apply le_trans (Nat.le_max_right _ _) hn
      -- e / 2 + e / 2 = e.
      _ = e := by ring
  · push_neg
    -- Show that there exist x(n) and y(n) such that
    -- lim {x n} = 0, lim {y n} = 0 and lim {x n - y n} ≠ 0.
    -- Take x(n) = 0 and y(n) = 1 / n.
    use 0, fun n => 1 / n
    simp
    -- We have {1 / n} = 1 / n for all n ≥ 2.
    have h {n : ℕ} (hn : 2 ≤ n) : Int.fract ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ := by
      rw [Int.fract_eq_self]
      rify at hn
      refine ⟨by positivity, ?_⟩
      apply inv_lt_one_of_one_lt₀
      linarith
    constructor
    · -- Show that lim {1 / n} = 0.
      -- We have {1 / n} = 1 / n for sufficiently large n.
      have heq : (fun n : ℕ => (1 : ℝ) / n) =ᶠ[atTop] (fun n => Int.fract ((n : ℝ)⁻¹)) := by
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        use 2
        intro n hn
        simp
        symm
        exact h hn
      apply Tendsto.congr' heq
      -- The limit of 1 / n is 0.
      exact tendsto_one_div_atTop_nhds_zero_nat
    · -- Show that lim {0 - 1 / n} = 1 ≠ 0.
      suffices Tendsto (fun n : ℕ => Int.fract (-(n : ℝ)⁻¹)) atTop (𝓝 1) by
        intro h
        have := tendsto_nhds_unique this h
        norm_num at this
      -- We have {0 - 1 / n} = 1 - 1 / n for sufficiently large n.
      have heq : (fun n : ℕ => 1 - (1 : ℝ) / n) =ᶠ[atTop] (fun n => Int.fract (-(n : ℝ)⁻¹)) := by
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        use 2
        intro n hn
        rw [Int.fract_neg (by rw [h hn]; positivity)]
        simp [h hn]
      apply Tendsto.congr' heq
      nth_rw 3 [show (1 : ℝ) = 1 - 0 by ring]
      apply Tendsto.const_sub
      -- The limit of 1 / n is 0, so the limit of 1 - 1 / n is 1.
      exact tendsto_one_div_atTop_nhds_zero_nat