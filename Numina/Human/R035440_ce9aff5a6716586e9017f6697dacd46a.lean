import Mathlib

/- Given that the function $f(x) = \sin\left(x + \frac{\pi}{2}\right) + \cos\left(x - \frac{\pi}{2}\right) + m$ has a maximum value of $2\sqrt{2}$, determine the value of the real number $m$. -/
theorem algebra_9168 (f : ℝ → ℝ) (m : ℝ) (h₀ : ∀ x, f x = Real.sin (x + Real.pi / 2) + Real.cos (x - Real.pi / 2)+m) (hG: IsGreatest {f x | x:ℝ} (2*Real.sqrt 2)): m = Real.sqrt 2 := by
-- rewrite the condition hG
have h₁: ∃ x, f x = 2 * Real.sqrt 2 := hG.left
have h₂: ∀x, f x ≤ 2 * Real.sqrt 2 := by
  rw [IsGreatest, upperBounds] at hG
  simp at hG
  exact hG.right
--first, we prove f attains maximum at x = π/4
have hmax: ∀x:ℝ, Real.sin (x+Real.pi/2) + Real.cos (x-Real.pi/2) ≤ Real.sqrt 2 := by
  have ht1: Real.cos (Real.pi/2) = 0 := Real.cos_pi_div_two
  have ht2: Real.sin (Real.pi/2) = 1 := Real.sin_pi_div_two
  intro x
  -- notice thatsin(x+π/2)+cos(x-π/2) = cos x + sin x
  have ht3: Real.sin (x+ Real.pi/2) = Real.cos x := by
    rw [Real.sin_add]
    rw [ht1, ht2]
    simp
  have ht4: Real.cos (x - Real.pi/2) = Real.sin x := by
    rw [Real.cos_sub]
    rw [ht1, ht2]
    simp
  rw [ht3, ht4]
  -- cos x + sin x = √2 * sin (x+π/4)
  have ht5: Real.cos x +  Real.sin x = Real.sqrt 2 * Real.sin (x + Real.pi /4) := by
    have htt1: Real.sin (x+Real.pi/4) = Real.sin x / Real.sqrt 2 + Real.cos x / Real.sqrt 2 := by
      rw [Real.sin_add x (Real.pi/4)]
      have htt2: Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
      field_simp [add_mul]
      rw [mul_assoc, mul_assoc, htt2]
    rw [htt1]
    field_simp
    ring
  rw [ht5]
  -- √2 * sin (x+π/4) ≤ √2
  have ht6: Real.sqrt 2 * Real.sin (x+Real.pi/4) ≤ Real.sqrt 2 := by
    have htt1: Real.sin (x+Real.pi/4) ≤ 1 := Real.sin_le_one (x + Real.pi / 4)
    have htt2: 0 < Real.sqrt 2 := by norm_num
    exact (mul_le_iff_le_one_right htt2).mpr htt1
  exact ht6
rcases h₁ with ⟨k,hk⟩
rcases h₀ k with eqk
rw [hk] at eqk
-- √2+m is the maximum of f(x), and 2√2 is also the maximum of f(x). so we argue that √2+m=2√2, therefore m=√2
have eqk1: Real.sin (k+Real.pi/2) + Real.cos (k-Real.pi/2) = 2* Real.sqrt 2 - m := by simp [eqk]
rcases hmax k with hkmax
rw [eqk1] at hkmax
-- we argue two maximum must be equal by showing max1 ≤ max2 and max2 ≤ max1.
have ineqm1: m ≥ Real.sqrt 2 := by
  have: 2*Real.sqrt 2 - m + m ≤ Real.sqrt 2 + m := add_le_add_right hkmax m
  rw [sub_add_comm] at this
  simp at this
  linarith [this]
have ineqm2: m ≤ Real.sqrt 2 := by
  by_contra! mge
  rcases h₂ (Real.pi/4) with ht1
  rcases h₀ (Real.pi/4) with ht2
  rw [ht2] at ht1
  have: Real.sin (Real.pi / 4 + Real.pi / 2) + Real.cos (Real.pi / 4 - Real.pi / 2) = Real.sqrt 2 := by
    have htt1: Real.sin (Real.pi/4 + Real.pi / 2) = Real.sqrt 2 / 2 := by
      simp [Real.sin_add]
    have htt2: Real.cos (Real.pi / 4 - Real.pi / 2) = Real.sqrt 2 / 2 := by
      simp [Real.cos_sub]
    simp [htt1, htt2]
  rw [this] at ht1
  linarith [mge, ht1]
exact eq_of_le_of_le ineqm2 ineqm1