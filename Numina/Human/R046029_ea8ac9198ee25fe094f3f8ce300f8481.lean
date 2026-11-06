import Mathlib

open Real
open scoped BigOperators

/- Let $\alpha, \beta, \gamma$ be the angles of a triangle opposite to the sides $a, b, c$ respectively. Prove the inequality

$$
2\left(\cos ^{2} \alpha+\cos ^{2} \beta+\cos ^{2} \gamma\right) \geq \frac{a^{2}}{b^{2}+c^{2}}+\frac{b^{2}}{a^{2}+c^{2}}+\frac{c^{2}}{a^{2}+b^{2}}
$$ -/
theorem inequalities_604319 (α β γ : ℝ) (hα : α ∈ Set.Ioo 0 π) (hβ : β ∈ Set.Ioo 0 π) (hγ : γ ∈ Set.Ioo 0 π) (hsum : α + β + γ = π) (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hsinlaw : a / sin α = b / sin β ∧ b / sin β = c / sin γ) :
    2 * (cos α ^ 2 + cos β ^ 2 + cos γ ^ 2) ≥ a ^ 2 / (b ^ 2 + c ^ 2) + b ^ 2 / (a ^ 2 + c ^ 2) + c ^ 2 / (a ^ 2 + b ^ 2) := by
  -- Tidy up the sine law, so that (a, b, c) = D * (sin α, sin β, sin γ) for some D.
  let D := a / sin α
  -- Show that sin α ≠ 0.
  have hα' : sin α ≠ 0 := by
    rw [sin_ne_zero_iff]
    simp at hα
    intro n
    by_contra!
    rw [<-this] at hα
    have : 0 < (n : ℝ) ∧ (n : ℝ) < 1 := by
      exact ⟨by nlinarith, by nlinarith⟩
    norm_cast at this
    omega
  -- Show that a = D * sin α.
  have haα : a = D * sin α := by
    simp [D]
    rw [div_mul_cancel₀ _ hα']
  -- Similarly, tidy up the sine law for b and c.
  have hβ' : sin β ≠ 0 := by
    rw [sin_ne_zero_iff]
    simp at hβ
    intro n
    by_contra!
    rw [<-this] at hβ
    have : 0 < (n : ℝ) ∧ (n : ℝ) < 1 := by
      exact ⟨by nlinarith, by nlinarith⟩
    norm_cast at this
    omega
  have hbβ : b = D * sin β := by
    simp [D]
    rw [hsinlaw.1, div_mul_cancel₀ _ hβ']
  have hγ' : sin γ ≠ 0 := by
    rw [sin_ne_zero_iff]
    simp at hγ
    intro n
    by_contra!
    rw [<-this] at hγ
    have : 0 < (n : ℝ) ∧ (n : ℝ) < 1 := by
      exact ⟨by nlinarith, by nlinarith⟩
    norm_cast at this
    omega
  have hcγ : c = D * sin γ := by
    simp [D]
    rw [hsinlaw.1, hsinlaw.2, div_mul_cancel₀ _ hγ']
  -- Show also that D ≠ 0.
  have hD : D ≠ 0 := by
    by_contra!
    rw [this] at haα
    linarith
  -- Substitute (a, b, c) = D * (sin α, sin β, sin γ) into the inequality.
  rw [haα, hbβ, hcγ]
  repeat rw [mul_pow]
  repeat rw [<-mul_add]
  repeat rw [mul_div_mul_left _ _ (show D ^ 2 ≠ 0 by simp; exact hD)]
  -- Show that sin² α ≤ (sin² β + sin² γ)(cos² γ + cos² β).
  have h₀ : sin α ^ 2 ≤ (sin β ^ 2 + sin γ ^ 2) * (cos γ ^ 2 + cos β ^ 2) := by
    calc
      sin α ^ 2 = sin (β + γ) ^ 2 := by
        -- First use the fact that α = π - β - γ.
        congrm ?_ ^ 2
        rw [show β + γ = π - α by linarith, sin_pi_sub]
      _ = (sin β * cos γ + sin γ * cos β) ^ 2 := by
        -- Use the sine addition formula.
        congrm ?_ ^ 2
        rw [sin_add β γ]
        ac_rfl
      _ ≤ (sin β ^ 2 + sin γ ^ 2) * (cos γ ^ 2 + cos β ^ 2) := by
        -- Apply the Cauchy-Schwarz inequality, which is essentially equivalent to (sin β - cos γ) ^ 2 + (cos γ - sin β) ^ 2 ≥ 0.
        linarith only [sq_nonneg (sin β * cos β - sin γ * cos γ)]
  -- Prove similar inequalities for sin² β and sin² γ.
  have h₁ : sin β ^ 2 ≤ (sin α ^ 2 + sin γ ^ 2) * (cos α ^ 2 + cos γ ^ 2) := by
    calc
      sin β ^ 2 = sin (α + γ) ^ 2 := by
        -- First use the fact that β = π - α - γ.
        congrm ?_ ^ 2
        rw [show α + γ = π - β by linarith, sin_pi_sub]
      _ = (sin α * cos γ + sin γ * cos α) ^ 2 := by
        -- Use the sine addition formula.
        congrm ?_ ^ 2
        rw [sin_add α γ]
        ac_rfl
      _ ≤ (sin α ^ 2 + sin γ ^ 2) * (cos α ^ 2 + cos γ ^ 2) := by
        -- Apply the Cauchy-Schwarz inequality.
        linarith only [sq_nonneg (sin α * cos α - sin γ * cos γ)]
  have h₂ : sin γ ^ 2 ≤ (sin α ^ 2 + sin β ^ 2) * (cos β ^ 2 + cos α ^ 2) := by
    calc
      sin γ ^ 2 = sin (α + β) ^ 2 := by
        -- First use the fact that γ = π - α - β.
        congrm ?_ ^ 2
        rw [show α + β = π - γ by linarith, sin_pi_sub]
      _ = (sin α * cos β + sin β * cos α) ^ 2 := by
        -- Use the sine addition formula.
        congrm ?_ ^ 2
        rw [sin_add α β]
        ac_rfl
      _ ≤ (sin α ^ 2 + sin β ^ 2) * (cos β ^ 2 + cos α ^ 2) := by
        -- Apply the Cauchy-Schwarz inequality.
        linarith only [sq_nonneg (sin α * cos α - sin β * cos β)]
  -- Combine these inequalities to get the desired result.
  calc
    2 * (cos α ^ 2 + cos β ^ 2 + cos γ ^ 2) = (cos γ ^ 2 + cos β ^ 2) + (cos α ^ 2 + cos γ ^ 2) + (cos β ^ 2 + cos α ^ 2) := by ring
    _ ≥ sin α ^ 2 / (sin β ^ 2 + sin γ ^ 2) + sin β ^ 2 / (sin α ^ 2 + sin γ ^ 2) + sin γ ^ 2 / (sin α ^ 2 + sin β ^ 2) := by
      -- Use h₀, h₁, h₂ repsectively for each term.
      iterate 2 apply add_le_add
      . rw [div_le_iff₀, mul_comm]
        exact h₀
        by_contra!
        have : sin γ ^ 2 = 0 := by
          linarith only [this, sq_nonneg (sin β), sq_nonneg (sin γ)]
        simp at this
        absurd this
        apply hγ'
      . rw [div_le_iff₀, mul_comm]
        exact h₁
        by_contra!
        have : sin α ^ 2 = 0 := by
          linarith only [this, sq_nonneg (sin α), sq_nonneg (sin γ)]
        simp at this
        absurd this
        apply hα'
      . rw [div_le_iff₀, mul_comm]
        exact h₂
        by_contra!
        have : sin β ^ 2 = 0 := by
          linarith only [this, sq_nonneg (sin α), sq_nonneg (sin β)]
        simp at this
        absurd this
        apply hβ'
