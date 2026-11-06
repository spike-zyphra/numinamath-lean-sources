import Mathlib

/- Trouver tous les nombres réels $x$ et $y$ tels que

$$
\left(x-\sqrt{x^{2}+1}\right)\left(y-\sqrt{y^{2}+1}\right)=1 \text { et }\left(x^{2}+y+2\right)\left(y^{2}+x+2\right)=8 .
$$ -/
theorem algebra_604844 :
    {(x, y) : ℝ × ℝ | (x - Real.sqrt (x ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = 1 ∧ (x ^ 2 + y + 2) * (y ^ 2 + x + 2) = 8} = {(1, -1), (-1, 1)} := by
  -- Break the goal into two parts.
  ext ⟨x, y⟩
  simp
  apply Iff.intro
  . -- First show that the simultaneous equations implies (x, y) = (1, -1) or (-1, 1)
    rintro ⟨h₀, h₁⟩
    -- Show that x ≠ Real.sqrt (x ^ 2 + 1) and y ≠ Real.sqrt (y ^ 2 + 1)
    have h₂ : Real.sqrt (x ^ 2 + 1) - x ≠ 0 := by
      -- Assume x = Real.sqrt (x ^ 2 + 1) and derive a contradiction.
      intro h₂
      rw [sub_eq_zero] at h₂
      replace h₂ : x ^ 2 = (Real.sqrt (x ^ 2 + 1)) ^ 2 := by nth_rw 1 [h₂]
      rw [Real.sq_sqrt (by positivity)] at h₂
      linarith only [h₂]
    have h₃ : Real.sqrt (y ^ 2 + 1) - y ≠ 0 := by
      -- Assume y = Real.sqrt (y ^ 2 + 1) and derive a contradiction.
      intro h₃
      rw [sub_eq_zero] at h₃
      replace h₃ : y ^ 2 = (Real.sqrt (y ^ 2 + 1)) ^ 2 := by nth_rw 1 [h₃]
      rw [Real.sq_sqrt (by positivity)] at h₃
      linarith only [h₃]
    rw [<-neg_sub] at h₀
    nth_rw 2 [<-neg_sub] at h₀
    rw [neg_mul_neg] at h₀
    -- Show that Real.sqrt (x ^ 2 + 1) - x = Real.sqrt (y ^ 2 + 1) + y by multiplying both sides by (Real.sqrt (y ^ 2 + 1) - y).
    have h₄ : Real.sqrt (x ^ 2 + 1) - x = Real.sqrt (y ^ 2 + 1) + y := by
      rw [<-mul_left_inj' h₃, h₀, <-sq_sub_sq, Real.sq_sqrt (by positivity)]
      simp
    -- Show that Real.sqrt (x ^ 2 + 1) + x = Real.sqrt (y ^ 2 + 1) - y by multiplying both sides by (Real.sqrt (x ^ 2 + 1) - y).
    have h₅ : Real.sqrt (x ^ 2 + 1) + x = Real.sqrt (y ^ 2 + 1) - y := by
      rw [<-mul_right_inj' h₂, h₀, mul_comm, <-sq_sub_sq, Real.sq_sqrt (by positivity)]
      simp
    -- Combine the two equations above to get x = -y.
    have h₆ : x = -y := by
      linarith only [h₄, h₅]
    -- Substitute x = -y into the second equation.
    simp [h₆] at h₁
    -- Let z = y² and change the equation to a quadratic equation in z.
    let z := y ^ 2
    rw [show y ^ 2 + y + 2 = (y ^ 2 + 2) + y by ac_rfl, show y ^ 2 + -y + 2 = (y ^ 2 + 2) - y by ring, <-sq_sub_sq, show y ^ 2 = z by rfl] at h₁
    -- We have (z + 4)(z - 1) = 0.
    replace h₁ : (z + 4) * (z - 1) = 0 := by linarith only [h₁]
    -- Note that z ≥ 0, so z = 1.
    simp [show z + 4 ≠ 0 by simp [z]; positivity] at h₁
    rw [show z = y ^ 2 by rfl, show (1 : ℝ) = 1 ^ 2 by norm_num, sq_sub_sq] at h₁
    -- Now (y + 1)(y - 1) = 0, so y = ±1.
    simp at h₁
    cases h₁ with
    | inl h₁ =>
      -- If y = -1, then x = 1.
      left
      exact ⟨by linarith , by linarith⟩
    | inr h₁ =>
      -- If y = 1, then x = -1.
      right
      exact ⟨by linarith , by linarith⟩
  . -- Now show that (x, y) = (1, -1) and (-1, 1) both satisfy the simultaneous equations.
    intro h
    obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := h
    . simp [hx, hy]
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    . simp [hx, hy]
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
