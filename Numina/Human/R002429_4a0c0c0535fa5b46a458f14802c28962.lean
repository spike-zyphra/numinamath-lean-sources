set_option maxHeartbeats 500000 -- we need lots of linariths
theorem aime_730 {x y z : ℝ} {m n : ℕ}
  (h0 : x^2 ≥ 1/25 ∧ y^2 ≥ 1/16 ∧ z^2 ≥ 1/16 ∧ x > 0 ∧ y > 0 ∧ z > 0) -- added hypothesis to make square roots valid
  (h1 : x = √(y^2 - 1/16) + √(z^2 - 1/16))
  (h2 : y = √(z^2 - 1/25) + √(x^2 - 1/25))
  (h3 : z = √(x^2 - 1/36) + √(y^2 - 1/36)) :
  ∃m n : ℕ, x + y + z = m / √(↑n : ℝ) ∧ m + n = 9 ∧ Squarefree n := by
    -- we rewrite the identity as a polynomial
    have h1₁ : x^4 + y^4 + z^4 - 2*x^2*y^2 - 2*x^2*z^2 - 2*y^2*z^2 = -4*x^2/16 := by
      -- first get rid of a radical
      have h1₃ : (x - √(z^2 - 1/16))^2 = y^2-1/16 := by
        rw [h1]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
      have h1₄ : x^2 - 2*x*√(z^2 - 1/16) + z^2 - 1/16 = y^2-1/16 := by
        rw [← h1₃]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring_nf
      have h1₅ : x^2 + z^2 - y^2 = 2*x*√(z^2 - 1/16) := by linarith
      -- then get rid of the other radical
      have h1₆ : (x^2 + z^2 - y^2)^2 = 4*x^2*(z^2 - 1/16) := by
        have := congrFun (congrArg HPow.hPow h1₅) 2 -- again done by squaring
        ring_nf at this
        rw [Real.sq_sqrt (by linarith)] at this
        ring_nf
        rw [this]
        ring_nf
      linarith
    -- we rewrite the identity as a polynomial
    have h2₁ : x^4 + y^4 + z^4 - 2*x^2*y^2 - 2*x^2*z^2 - 2*y^2*z^2 = -4*y^2/25 := by
      -- first get rid of a radical
      have h2₃ : (y - √(x^2 - 1/25))^2 = z^2-1/25 := by
        rw [h2]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
      have h2₄ : y^2 - 2*y*√(x^2 - 1/25) + x^2 - 1/25 = z^2-1/25 := by
        rw [← h2₃]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring_nf
      have h2₅ : x^2 + y^2 - z^2 = 2*y*√(x^2 - 1/25) := by linarith
      -- then get rid of the other radical
      have h2₆ : (x^2 + y^2 - z^2)^2 = 4*y^2*(x^2 - 1/25) := by
        have := congrFun (congrArg HPow.hPow h2₅) 2 -- again done by squaring
        ring_nf at this
        rw [Real.sq_sqrt (by linarith)] at this
        ring_nf
        rw [this]
        ring_nf
      linarith
    -- we rewrite the identity as a polynomial
    have h3₁ : x^4 + y^4 + z^4 - 2*x^2*y^2 - 2*x^2*z^2 - 2*y^2*z^2 = -4*z^2/36 := by
      -- first get rid of a radical
      have h3₃ : (z - √(y^2 - 1/36))^2 = x^2-1/36 := by
        rw [h3]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
      have h3₄ : z^2 - 2*z*√(y^2 - 1/36) + y^2 - 1/36 = x^2-1/36 := by
        rw [← h3₃]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring_nf
      have h3₅ : y^2 + z^2 - x^2 = 2*z*√(y^2 - 1/36) := by linarith
      -- then get rid of the other radical
      have h3₆ : (y^2 + z^2 - x^2)^2 = 4*z^2*(y^2 - 1/36) := by
        have := congrFun (congrArg HPow.hPow h3₅) 2 -- again done by squaring
        ring_nf at this
        rw [Real.sq_sqrt (by linarith)] at this
        ring_nf
        rw [this]
        ring_nf
      linarith
    -- now combine the polynomial identities, since their LHS are the same
    have hxy : x = 4/5*y := by
      have : x^2 = (4/5*y)^2 := by linarith
      rw [pow_left_inj₀ (by linarith) (by linarith) (by linarith)] at this
      exact this
    have hyz : y = 5/6*z := by
      have : y^2 = (5/6*z)^2 := by linarith
      rw [pow_left_inj₀ (by linarith) (by linarith) (by linarith)] at this
      exact this
    -- now we obtain an equation in a single variable
    rw [hxy,hyz] at h1₁
    have hz := sub_eq_zero_of_eq h1₁
    ring_nf at hz
    -- we deduce the value of z^2
    have hz : 16 = 175*z^2 := by
      have : 16*z^2 = 175*z^2*z^2 := by linarith
      exact GroupWithZero.mul_left_injective (by linarith) this
    -- and the value of z by solving the equation
    have hz : z = 4 / (5*√7) := by
      have : z^2 = (4/(5*√7))^2 := by
        ring_nf
        rw [inv_pow,Real.sq_sqrt]
        linarith
        linarith
      rw [pow_left_inj₀ (by linarith) _ (by linarith)] at this
      exact this
      -- we need to help Lean4/Mathlib understand that expressions in √7 are positive
      have : 0 < 5*√7 := mul_pos_iff.mpr (Or.inl ⟨Nat.ofNat_pos,Real.sqrt_pos.mpr Nat.ofNat_pos⟩)
      rw [le_div_iff₀ this]
      linarith
    -- this is the goal we have to express in terms of m,n
    have hxyz : x + y + z = 2/√7 := by
      rw [hxy,hyz,hz]
      ring_nf
    use 2, 7
    -- help Lean4/Mathlib understand that 7 is square-free. For this,
    -- we show that any divisor of 7 has to be 1 or 7; considering the
    -- divisor 7, its square 49 does not divide 7, as is discovered by omega.
    have sqfree_7 : Squarefree 7 := by
      intros x xxdiv
      rw [Nat.isUnit_iff]
      have div_7 : Nat.divisors 7 = {1,7} := by decide
      have xxdiv : (x * x ∣ 7) ∧ (7 ≠ 0) := ⟨xxdiv,by linarith⟩
      rw [← Nat.mem_divisors,div_7,Finset.mem_insert,Finset.mem_singleton] at xxdiv
      cases xxdiv with
      | inl h => exact Nat.eq_one_of_mul_eq_one_right h
      | inr h => { have := dvd_of_eq h.symm
                   rw [Nat.Prime.dvd_mul (by decide),or_self] at this
                   have : 49 ∣ x*x := mul_dvd_mul this this
                   omega }
    exact ⟨hxyz,by linarith,sqfree_7⟩