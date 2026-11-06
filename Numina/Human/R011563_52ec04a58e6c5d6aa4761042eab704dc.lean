import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- For a real-valued function $f(x,y)$ of two positive real variables $x$ and $y$, define $f$ to be [i]linearly bounded[/i] if and only if there exists a positive number $K$ such that $|f(x,y)| < K(x+y)$ for all positive $x$ and $y.$ Find necessary and sufficient conditions on the real numbers $\alpha$ and $\beta$ such that $x^{\alpha}y^{\beta}$ is linearly bounded. -/
theorem calculus_36549 (α β : ℝ) :
  (∃ K > 0, ∀ {x y : ℝ}, x > 0 → y > 0 → |(x ^ α * y ^ β)| < K * (x + y)) ↔
  α + β = 1 ∧ α ≥ 0 ∧ β ≥ 0 := by 
/-
Suppose xᵃ yᵝ is linearly bounded.
• If α + β > 1, take x = y → ∞.  Contradiction.
• If α + β < 1, take x = y → 0.  Contradiction.
• If α < 0,     take x → 0, y = 1. Contradiction.
• If β < 0,     take y → 0, x = 1. Contradiction.
Hence α + β = 1 and α,β ≥ 0.

Conversely, if α + β = 1 with α,β ≥ 0, Young’s inequality/ AM-GM inequality
     xᵃ yᵝ ≤ α·x + β·y
gives the desired linear bound.

 A two–variable monomial is linearly bounded **iff**
its exponents are non-negative and sum to 1. -/

  --------------------------------------------------------------------------------
  -- ⇒  Direction:  bounded  ⇒  conditions on α,β
  -- (Each block mirrors one bullet of the informal proof.)
  --------------------------------------------------------------------------------
  constructor
  · intro hBound
    rcases hBound with ⟨K, Kpos, hK⟩

    /- **If `α < 0` pick `x → 0`, `y = 1`** -/
    have hα_nonneg : 0 ≤ α := by
      by_contra hαneg
      have hαneg' : α < 0 := by linarith
      -- Choose a *fixed* positive y and a *small* x
      -- we have 1 / (x ^ (-α) ) = 2 * K
      -- solved by x ^ (-α) = 1 / (2 * K)
      -- solved by (-α) * log x = log (1 / (2 * K))
      -- solved by x = exp (log (1 / (2 * K)) / (-α))
      -- solved by x = (1 / (3 * K)) ^ (-1 / α)
      let x₀ : ℝ := (1 / (1 + 3 * K)) ^ (1 / (-α))
      have hx₀ : x₀ > 0 := by
        have : (1 / (1 + 3 * K)) ^ (1 / (-α)) > 0 := by
          have exponent : 0 < (1 / (-α)) := by
            have : 0 < (-α) := by linarith [hαneg']
            apply one_div_pos.2 this
          have num : 0 < (1 / (1 + 3 * K)) := by
            have k0_pos : 0 < 1 + 3 * K := by
              have : 0 < 3 * K := by linarith
              linarith
            rw [one_div_pos]
            exact k0_pos
          refine (Real.rpow_pos_of_pos num _)
        exact this

      have hcontr := hK (show x₀ > 0 from hx₀) (show (1 : ℝ) > 0 from one_pos)
      simp at hcontr

      have hkpos : 0 <= 1 / (1 + 3 * K) := by
        have : 0 < 1 + 3 * K := by
          have : 0 < 3 * K := by linarith [Kpos]
          linarith
        apply le_of_lt
        apply one_div_pos.2 this

      --  As x₀ → 0 the left-hand side tends to ∞, contradicting the fixed right-hand bound.
      have h_simp : |x₀ ^ α| = x₀ ^ α := by simp [abs_of_pos (Real.rpow_pos_of_pos hx₀ α)]
      rw [h_simp] at hcontr
      have habs1 : |x₀ ^ α * 1 ^ β| < K * 2 := by
        -- Simplify the left side
        simp
        rw [h_simp]

        -- Show x₀ ≤ 1, so x₀ + 1 ≤ 2
        have hx₀_le_one : x₀ ≤ 1 := by
          -- x₀ = (1/(1+3K))^(1/(-α)) ≤ 1 since base < 1 and exponent > 0
          have h_base_lt_one : 1 / (1 + 3 * K) ≤ 1 :=
            div_le_one_of_le₀ (by linarith [Kpos]) (by linarith [Kpos])
          have h_exp_pos : 0 < 1 / (-α) := one_div_pos.2 (by linarith [hαneg'])
          unfold x₀
          apply Real.rpow_le_one _ h_base_lt_one (by linarith [h_exp_pos])
          exact hkpos

        -- Chain the inequalities: x₀ ≤ 1 → x₀ + 1 ≤ 2 → K(x₀ + 1) ≤ K·2
        calc x₀ ^ α
          < K * (x₀ + 1)  := hcontr
          _ ≤ K * 2       := mul_le_mul_of_nonneg_left (by linarith [hx₀_le_one]) (by linarith [Kpos])

      have habs2 : |x₀ ^ α * 1 ^ β| >= K * 2 := by
        simp
        rw [h_simp]
        unfold x₀
        rw [<- Real.rpow_mul hkpos]
        have : (1/ -α) * α = -1 := by
          calc (1/ -α) * α
            = α/(-α) := by rewrite (occs := .pos [2]) [<- mul_one_div]; rw [mul_comm]
            _ = -(α/α) := by rw [div_neg]
            _ = -1 := by rw [div_self]; linarith
        rw [this]
        rw [Real.rpow_neg hkpos]
        rw [Real.rpow_one]
        rw [inv_eq_one_div]
        simp
        linarith

      have habs : |x₀ ^ α * 1 ^ β| < K * 2 /\ |x₀ ^ α * 1 ^ β| ≥ K * 2 := by
        constructor
        exact habs1
        exact habs2

      -- Contract habs1 and habs2
      have : False := by linarith [habs1, habs2]
      exact this

    /- **If `β < 0` pick `y → 0`, `x = 1`** -/
    have hβ_nonneg : 0 ≤ β := by
      by_contra hβneg
      -- completely analogous to the α-case
      let x₀ : ℝ := (1 / (1 + 3 * K)) ^ (1 / (-β))
      have hx₀ : x₀ > 0 := by
        have : (1 / (1 + 3 * K)) ^ (1 / (-β)) > 0 := by
          have exponent : 0 < (1 / (-β)) := by
            have : 0 < (-β) := by linarith [hβneg]
            apply one_div_pos.2 this
          have num : 0 < (1 / (1 + 3 * K)) := by
            have k0_pos : 0 < 1 + 3 * K := by
              have : 0 < 3 * K := by linarith
              linarith
            rw [one_div_pos]
            exact k0_pos
          refine (Real.rpow_pos_of_pos num _)
        exact this

      have hcontr := hK (show (1 : ℝ) > 0 from one_pos) (show x₀ > 0 from hx₀)
      simp at hcontr

      have hkpos : 0 <= 1 / (1 + 3 * K) := by
        have : 0 < 1 + 3 * K := by
          have : 0 < 3 * K := by linarith [Kpos]
          linarith
        apply le_of_lt
        apply one_div_pos.2 this

      --  As x₀ → 0 the left-hand side tends to ∞, contradicting the fixed right-hand bound.
      have h_simp : |x₀ ^ β| = x₀ ^ β := by simp [abs_of_pos (Real.rpow_pos_of_pos hx₀ β)]
      rw [h_simp] at hcontr
      have habs1 : |x₀ ^ β * 1 ^ β| < K * 2 := by
        -- Simplify the left side
        simp
        rw [h_simp]

        -- Show x₀ ≤ 1, so x₀ + 1 ≤ 2
        have hx₀_le_one : x₀ ≤ 1 := by
          -- x₀ = (1/(1+3K))^(1/(-β)) ≤ 1 since base < 1 and exponent > 0
          have h_base_lt_one : 1 / (1 + 3 * K) ≤ 1 :=
            div_le_one_of_le₀ (by linarith [Kpos]) (by linarith [Kpos])
          have h_exp_pos : 0 < 1 / (-β) := one_div_pos.2 (by linarith [hβneg])
          unfold x₀
          apply Real.rpow_le_one _ h_base_lt_one (by linarith [h_exp_pos])
          exact hkpos

        -- Chain the inequalities: x₀ ≤ 1 → x₀ + 1 ≤ 2 → K(x₀ + 1) ≤ K·2
        calc x₀ ^ β
          < K * (1 + x₀)  := hcontr
          _ ≤ K * 2       := mul_le_mul_of_nonneg_left (by linarith [hx₀_le_one]) (by linarith [Kpos])

      have habs2 : |x₀ ^ β * 1 ^ β| >= K * 2 := by
        simp
        rw [h_simp]
        unfold x₀
        rw [<- Real.rpow_mul hkpos]
        have : (1/ -β) * β = -1 := by
          calc (1/ -β) * β
            = β/(-β) := by rewrite (occs := .pos [2]) [<- mul_one_div]; rw [mul_comm]
            _ = -(β/β) := by rw [div_neg]
            _ = -1 := by rw [div_self]; linarith
        rw [this]
        rw [Real.rpow_neg hkpos]
        rw [Real.rpow_one]
        rw [inv_eq_one_div]
        simp
        linarith

      have habs : |x₀ ^ β * 1 ^ β| < K * 2 /\ |x₀ ^ β * 1 ^ β| ≥ K * 2 := by
        constructor
        exact habs1
        exact habs2

      -- Contract habs1 and habs2
      have : False := by linarith [habs1, habs2]
      exact this

    /- **If `α + β ≠ 1`**
       *case 1* `α+β > 1`: take x = y → ∞.
       *case 2* `α+β < 1`: take x = y → 0. -/
    have hsum : α + β = 1 := by
      by_contra hneq
      have hcases : α + β < 1 ∨ 1 < α + β:= by
        have : α + β ≤ 1 ∨ α + β ≥ 1 := le_total _ _
        cases this with
        | inl hle =>
            have hlt : α + β < 1 := lt_of_le_of_ne hle hneq
            exact Or.inl hlt
        | inr hge =>
            have hgt : 1 < α + β := by
              apply lt_of_le_of_ne _ _
              simp at hge
              exact hge
              simp
              unfold Not at hneq
              unfold Not
              intro h
              apply hneq
              eapply Eq.symm h
            exact Or.inr hgt

      cases hcases with
      | inl hlt =>
          -- pick x = y very small
          -- x = y means f(x,y) = x^{α + β} = x^{1-ε} where ε > 0
          -- meanwhile 2 * K * x does not tend to 0 as fast
          -- we have by hK that |x^{α + β}| < K * 2 * x
          -- so just find some x small enough such that x / x^ε >= 2 * K * x
          -- ie such that 1 / x^ε >= 2 * K
          -- solved by x^ε = 1 / (2 * K)
          -- solved by ε * log x = log (1 / (2 * K))
          -- solved by x = exp (log (1 / (2 * K)) / (ε))
          -- solved by x = (1 / (2 * K)) ^ (1 / ε)
          let ε : ℝ := 1 - (α + β)
          have hεpos : ε > 0 := by unfold ε; linarith [hlt]
          let x₀ : ℝ := (1 / (2 * K)) ^ (1 / ε)
          have hx₀ : x₀ > 0 := by
            have : (1 / (2 * K)) ^ (1 / ε) > 0 := by
              have exponent : 0 < (1 / ε) := by
                apply one_div_pos.2 hεpos
              have num : 0 < (1 / (2 * K)) := by
                have k0_pos : 0 < 2 * K := by linarith [Kpos]
                apply one_div_pos.2 k0_pos
              apply Real.rpow_pos_of_pos num
            exact this
          have hcontr1 := hK (show x₀ > 0 from hx₀) (show x₀ > 0 from hx₀)

          have hαβ : α + β = 1 - ε := by unfold ε; linarith
          have hcontr2 : x₀ ^ (α + β) = K * 2 * x₀ := by
            rw [hαβ]
            rw [Real.rpow_sub]
            simp
            rw [(show x₀ / x₀ ^ ε = x₀ * (1/x₀^ε) from by ring)]
            rw [(show K * 2 * x₀ = x₀ * (2 * K) from by ring)]
            rw [mul_cancel_left_mem_nonZeroDivisors]
            rw [<- Real.rpow_mul]
            have : 1/ε * ε = 1 := by
              rw [(show 1/ε * ε = ε / ε from by ring)]
              apply div_self
              linarith [hεpos]
            rw [this]
            simp
            have : 0 < 2 * K := by linarith [Kpos]
            have : 0 < 1 / (2 * K) := by
              apply one_div_pos.2 this
            linarith [this]
            rw [mem_nonZeroDivisors_iff_ne_zero]
            linarith [hx₀]
            exact hx₀
    
          rw [rpow_add hx₀] at hcontr2

          -- prove contradiction
          have : False := by
            rw [hcontr2] at hcontr1
            -- show |K * 2 * x₀| = K * 2 * x₀
            have hpos : K * 2 * x₀ > 0 := by
              have hKpos := mul_pos Kpos (mul_pos zero_lt_two hx₀)
              linarith [hKpos]
            rw [(abs_of_pos hpos)] at hcontr1
            linarith [hcontr1]
          exact this

      | inr hgt =>
          -- pick x = y very large
          -- x = y means f(x,y) = x^{α + β} = x^{1+ε} where ε > 0
          -- meanwhile 2 * K * x does not tend to ∞ as fast
          -- so we have by hK that |x^{α + β}| < K * 2 * x
          -- then we pick some x large enough such that x^{α + β} = K * 2 * x
          -- if ε = 1 - (α + β) > 0, then we have
          -- x^{α + β} = K * 2 * x  <=>  x = (K * 2) ^ (1 / ε)
          let ε : ℝ := (α + β) - 1
          have hεpos : ε > 0 := by unfold ε; linarith [hgt]
          let x₀ : ℝ := (K * 2) ^ (1 / ε)
          have hx₀ : x₀ > 0 := by
            have : (K * 2) ^ (1 / ε) > 0 := by
              have exponent : 0 < (1 / ε) := by
                apply one_div_pos.2 hεpos
              have num : 0 < (K * 2) := by linarith [Kpos]
              apply Real.rpow_pos_of_pos num
            exact this
          have hcontr1 := hK (show x₀ > 0 from hx₀) (show x₀ > 0 from hx₀)
          have hαβ : α + β = 1 + ε := by unfold ε; linarith

          have hcontr2 : x₀ ^ (α + β) = K * 2 * x₀ := by
            rw [hαβ]
            rw [Real.rpow_add hx₀]
            simp
            rw [(show K * 2 * x₀ = x₀ * (2 * K) from by ring)]
            rw [mul_cancel_left_mem_nonZeroDivisors]
            rw [<- Real.rpow_mul]
            have : 1/ε * ε = 1 := by
              rw [(show 1/ε * ε = ε / ε from by ring)]
              apply div_self
              linarith [hεpos]
            rw [this]
            simp
            linarith
            linarith
            rw [mem_nonZeroDivisors_iff_ne_zero]
            linarith [hx₀]

          rw [rpow_add hx₀] at hcontr2

          -- prove contradiction
          have : False := by
            rw [hcontr2] at hcontr1
            -- show |K * 2 * x₀| = K * 2 * x₀
            have hpos : K * 2 * x₀ > 0 := by
              have hKpos := mul_pos Kpos (mul_pos zero_lt_two hx₀)
              linarith [hKpos]
            rw [(abs_of_pos hpos)] at hcontr1
            linarith [hcontr1]
          exact this

    exact ⟨hsum, hα_nonneg, hβ_nonneg⟩

  --------------------------------------------------------------------------------
  -- ⇐  Direction:  conditions  ⇒  monomial is linearly bounded
  --------------------------------------------------------------------------------
  · rintro ⟨hsum, hα_nonneg, hβ_nonneg⟩

      -- This is precisely the usual Young (or weighted AM-GM) inequality.
      -- Real.geom_mean_le_arith_mean2_weighted

    -- Pick a convenient constant `K`.
    let K : ℝ := max α β + 1
    have Kpos : K > 0 := by
      have : max α β ≥ 0 := by
        apply le_max_iff.mpr
        exact Or.inl hα_nonneg
      have : max α β + 1 > 0 := by linarith
      unfold K; linarith

    refine ⟨K, Kpos, ?_⟩
    intro x y hx hy
    -- Chain of inequalities:
    -- |xᵃ yᵝ|   =   xᵃ yᵝ                (x,y > 0)
    --           ≤   α·x + β·y            (Young)
    --           ≤   x + βy
    --           ≤   (max α β)(x + y) (because α,β ≤ max α β, x,y ≥ 0)
    calc |x ^ α * y ^ β|
      =  x ^ α * y ^ β := by
          apply abs_of_pos
          apply mul_pos
          apply Real.rpow_pos_of_pos hx α
          apply Real.rpow_pos_of_pos hy β
      _ <= α * x + β * y := by
        apply Real.geom_mean_le_arith_mean2_weighted
        exact hα_nonneg
        exact hβ_nonneg
        exact (le_of_lt hx)
        exact (le_of_lt hy)
        exact hsum
      _ <= (max α β) * (x + y) := by
        have hx_nonneg : (0 : ℝ) ≤ x := le_of_lt hx
        have hy_nonneg : (0 : ℝ) ≤ y := le_of_lt hy
        have hα : α ≤ max α β := by
          have : α ≤ max α β := le_max_left _ _
          linarith
        have hβ : β ≤ max α β := by
          have : β ≤ max α β := le_max_right _ _
          linarith
        have hαx : α * x <= (max α β) * x :=
          mul_le_mul_of_nonneg_right hα hx_nonneg
        have hβy : β * y <= (max α β) * y :=
          mul_le_mul_of_nonneg_right hβ hy_nonneg
        have : α * x + β * y <= (max α β) * x + (max α β) * y := by
          linarith
        linarith [this]
      _ < K * (x + y) := by
        unfold K
        linarith
