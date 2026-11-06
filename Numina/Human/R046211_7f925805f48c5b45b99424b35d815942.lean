import Mathlib

open Real Set
open scoped BigOperators

/- 19. Let $x$ be a positive real number. What is the maximum value of $\frac{2022 x^{2} \log (x+2022)}{(\log (x+2022))^{3}+2 x^{3}}$ ? -/
theorem algebra_225892 (x : ℝ) (hx : x > 0) :
    IsGreatest {y | ∃ x : ℝ, x > 0 ∧ y = 2022 * x^2 * log (x + 2022) / ((log (x + 2022))^3 + 2 * x^3)} 674 := by
  constructor
  -- proving there is a x that evaluates to 674
  -- firrst we'll prove there is x such that x = log (x + 2022), define f, g, s to use intermediate value theorem
  . let f := fun (x : ℝ) ↦ x
    let g := fun (x : ℝ) ↦ log (x + 2022)
    let s := Icc (0: ℝ) 2022
    -- we use intermediate value theorem on [0, 2022]
    have : ∃ x ∈ s, f x = g x := by
      apply IsPreconnected.intermediate_value₂ (s := s) (a := 0) (b := 2022)
      any_goals simp [s]
      . exact isPreconnected_Icc
      . simp [f]
        exact continuousOn_id' (Icc 0 2022)
      . rw [show g = (log · ) ∘ (· + 2022) by ext x; simp]
        apply ContinuousOn.comp (t := {0}ᶜ)
        . exact continuousOn_log
        . apply Continuous.continuousOn
          exact continuous_add_right 2022
        . simp [MapsTo]
          rintro x hx₁ hx₂
          linarith
      . simp [f, g]
        exact log_nonneg (by norm_num)
      -- for log (2022 + 2022) < 2022, use bounds of log 2
      . simp [f, g]
        rw [show (2022: ℝ) + 2022 = 2 * 2022 by norm_num, log_mul (by norm_num) (by norm_num)]
        nth_rw 2 [show (2022: ℝ) = 1 + (2022 - 1) by norm_num]
        gcongr
        . linarith [Real.log_two_lt_d9 ]
        . exact Real.log_le_sub_one_of_pos (by norm_num)
    obtain ⟨x, hxs, hx⟩ := this
    -- show that the x is not 0,
    have hxz : x ≠ 0 := by
      by_contra hx'
      rw [hx'] at hx
      simp [f, g] at hx
      have : 0 < log 2022 := log_pos (by norm_num)
      linarith
    -- now we can just plug in x
    simp [f, g] at hx
    use x
    and_intros
    . simp [s] at hxs
      change 0 < x
      apply lt_of_le_of_ne
      . exact hxs.left
      . exact hxz.symm
    . rw [← hx]
      ring_nf
      field_simp
  -- now proving 674 is an upper bound
  . rintro y
    simp
    rintro x hx hy
    rw [hy]
    -- we first prove a lemma that is a conveniant version of am-gm
    have amgm3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * a * b * c ≤ a^3 + b^3 + c^3 := by
      have ha' : 0 ≤ a^3 := by positivity
      have hb' : 0 ≤ b^3 := by positivity
      have hc' : 0 ≤ c^3 := by positivity
      have : (0 : ℝ) ≤ 1 / 3 := by norm_num
      have h := Real.geom_mean_le_arith_mean3_weighted this this this ha' hb' hc' (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast] at h
      rw [← Real.rpow_mul ha, ← Real.rpow_mul hb, ← Real.rpow_mul hc] at h
      simp at h
      norm_cast at h
      linear_combination 3 * h
    have hlog : 0 < log (x + 2022) := log_pos (by linarith)
    -- now we prove the inquality, by usign am-gm on denominator
    calc
      _ = 2022 * x ^ 2 * log (x + 2022) / (log (x + 2022) ^ 3 + x ^ 3 + x ^ 3) := by ring
      _ ≤ 2022 * x ^ 2 * log (x + 2022) / (3 * log (x + 2022) * x  * x ) := by
        gcongr
        apply amgm3
        . exact le_of_lt hlog
        . exact le_of_lt hx
        . exact le_of_lt hx
      _ = 674 := by
        field_simp
        ring