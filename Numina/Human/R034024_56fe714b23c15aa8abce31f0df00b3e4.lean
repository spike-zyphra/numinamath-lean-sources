import Mathlib

/- Let $a,$ $b,$ $c,$ $d$ be real numbers such that $a + b + c + d = 17$ and $ab + bc + cd + da = 46.$  Find the minimum possible value of $a^2 + b^2 + c^2 + d^2.$ -/
theorem algebra_21777 :
    IsLeast {x | ∃ a b c d : ℝ, a + b + c + d = 17 ∧ a * b + b * c + c * d + d * a = 46 ∧ x = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2} (197 / 2) := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  let r : ℝ := (17 + Real.sqrt 105) / 2
  let s : ℝ := (17 - Real.sqrt 105) / 2
  refine ⟨?_, ?_⟩
  . -- Show that the minimum could be attained when taking a = c = r / 2, b = d = s / 2.
    use r / 2, s / 2, r / 2, s / 2
    ring_nf
    norm_num
  . -- Show that 197 / 2 is the lower bound of any possible value.
    intro x a b c d h₀ h₁ hx
    rw [hx]
    clear x hx
    replace h₁ := (show (a + c) * (b + d) = a * b + b * c + c * d + d * a by ring_nf).trans h₁
    replace h₀ := (show (a + c) + (b + d) = a + b + c + d by ac_rfl).trans h₀
    let r' : ℝ := a + c
    let s' : ℝ := b + d
    rw [show a + c = r' by dsimp, show b + d = s' by dsimp] at h₀ h₁
    symm at h₀
    rw [add_comm] at h₀
    apply sub_eq_of_eq_add at h₀
    rw [h₀.symm] at h₁
    have h₂ (r' : ℝ): r' * (17 - r') = 46 → (r' - r) * (r' - s) = 0 := by
      intro h₂
      ring_nf at h₂ ⊢
      norm_num
      linarith only [h₂]
    apply h₂ at h₁
    clear h₂
    simp at h₁
    -- There would be two cases: (r', s') = (r, s) or (s, r). Either case we could do the calculations.
    cases h₁ with
    | inl h₁ =>
      refine (show 197 / 2 ≤ (r ^ 2 + s ^ 2) / 2 by ring_nf; norm_num).trans ?_
      rw [<-@mul_div_cancel₀ _ _ 2 (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2), <-mul_div_assoc, div_le_div_right, show a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (a ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2) by ac_rfl, mul_add]
      refine add_le_add ?_ ?_
      . -- Show that r ^ 2 ≤ 2 * (a ^ 2 + c ^ 2).
        rw [show r = a + c by simp [show a + c = r' by simp [r']]; linarith only [h₁]]
        linarith only [show (a - c) ^ 2 ≥ 0 by positivity]
      . -- Show that s ^ 2 ≤ 2 * (b ^ 2 + d ^ 2).
        replace h₁ : s' - s = 0 := by
          linarith only [h₀, h₁, show r + s = 17 by ring_nf]
        rw [show s = b + d by simp [show b + d = s' by simp [r']]; linarith only [h₁]]
        linarith only [show (b - d) ^ 2 ≥ 0 by positivity]
      all_goals
        norm_num
    | inr h₁ =>
      refine (show 197 / 2 ≤ (r ^ 2 + s ^ 2) / 2 by ring_nf; norm_num).trans ?_
      rw [<-@mul_div_cancel₀ _ _ 2 (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2), <-mul_div_assoc, div_le_div_right, show a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (a ^ 2 + c ^ 2) + (b ^ 2 + d ^ 2) by ac_rfl, mul_add, add_comm (r ^ 2) (s ^ 2)]
      refine add_le_add ?_ ?_
      . -- Show that s ^ 2 ≤ 2 * (a ^ 2 + c ^ 2).
        rw [show s = a + c by simp [show a + c = r' by simp [r']]; linarith only [h₁]]
        linarith only [show (a - c) ^ 2 ≥ 0 by positivity]
      . -- Show that r ^ 2 ≤ 2 * (b ^ 2 + d ^ 2).
        replace h₁ : s' - r = 0 := by
          linarith only [h₀, h₁, show r + s = 17 by ring_nf]
        rw [show r = b + d by simp [show b + d = s' by simp [r']]; linarith only [h₁]]
        linarith only [show (b - d) ^ 2 ≥ 0 by positivity]
      all_goals
        norm_num
