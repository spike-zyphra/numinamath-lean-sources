import Mathlib

/- Let $a, b, c$ be positive reals. Prove that  $$ \left(a^{5}-a^{2}+3\right)\left(b^{5}-b^{2}+3\right)\left(c^{5}-c^{2}+3\right) \geq(a+b+c)^{3} . $$
-/
theorem inequalities_606386 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) ≥ (a + b + c) ^ 3 := by
  -- Show a lemma that x⁵ - x² + 3 ≥ x³ + 1 + 1.
  have h₁ (x : ℝ) (hx : 0 < x) : x ^ 5 - x ^ 2 + 3 ≥ x ^ 3 + 1 + 1 := by
    suffices h : 0 ≤ x ^ 5 - x ^ 2 + 3 - (x ^ 3 + 1 + 1) by
      rw [sub_nonneg] at h
      exact h
    rw [show x ^ 5 - x ^ 2 + 3 - (x ^ 3 + 1 + 1) = (x - 1) ^ 2 * (x + 1) * (x ^ 2 + x + 1) by ring_nf]
    -- This is equivalent to proving 0 ≤ (x - 1)²(x + 1)(x² + x + 1).
    positivity
  -- Prove the Cauchy-Schwarz inequality.
  have CS_ineq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) : (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), sq_nonneg (y₁ * z₂ - z₁ * y₂), sq_nonneg (z₁ * x₂ - x₁ * z₂)]
  -- Prove that (a³ + 1 + 1)(1 + b³ + 1) ≥ (a ^ (3 / 2) + b ^ (3 / 2) + 1)² using CS_ineq.
  have h₂ : (a ^ 3 + 1 + 1) * (1 + b ^ 3 + 1) ≥ (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ) + 1) ^ 2 := by
    specialize CS_ineq (a ^ (3 / 2 : ℝ)) 1 1 1 (b ^ (3 / 2 : ℝ)) 1
    iterate 2 rw [<-Real.rpow_natCast]
    rw [show (3 : ℕ) = (3 / 2 : ℝ) * 2 by norm_num, Real.rpow_mul, Real.rpow_mul]
    nth_rw 2 [show (2 : ℝ) = (2 : ℕ) by simp]
    nth_rw 3 [show (2 : ℝ) = (2 : ℕ) by simp]
    iterate 2 rw [Real.rpow_natCast]
    rw [one_pow, mul_one, one_mul, one_mul] at CS_ineq
    apply CS_ineq
    positivity
    positivity
  -- Prove that (a³ + 1 + 1)(1 + b³ + 1)(1 + 1 + c³) ≥ (a + b + c)³ using Holder's inequality.
  have h₃ : (a ^ 3 + 1 + 1) * (1 + b ^ 3 + 1) * (1 + 1 + c ^ 3) ≥ (a + b + c) ^ 3 := by
    calc
      (a ^ 3 + 1 + 1) * (1 + b ^ 3 + 1) * (1 + 1 + c ^ 3) ≥ (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ) + 1) ^ 2 * (1 + 1 + c ^ 3) := by
        apply mul_le_mul
        . apply h₂
        . rfl
        . positivity
        . positivity
      _ ≥ (a + b + c) ^ 3 := by
        let x (n : ℕ) : NNReal :=
          match n with
          | 0 => Real.toNNReal a
          | 1 => Real.toNNReal b
          | 2 => 1
          | _ => 0
        let y (n : ℕ) : NNReal :=
          match n with
          | 0 => 1
          | 1 => 1
          | 2 => Real.toNNReal c
          | _ => 0
        -- Apply Holder's inequality.
        have := @NNReal.inner_le_Lp_mul_Lq _ (Finset.range 3) x y (3 / 2) 3 (by rw [Real.isConjExponent_iff_eq_conjExponent]; norm_num; norm_num)
        iterate 9 rw [Finset.sum_range_succ] at this
        iterate 3 rw [Finset.sum_range_zero] at this
        simp [x, y, -one_div] at this
        -- Simplify all these "NNReal" stuff.
        rw [show (1 : NNReal) = (1 : ℝ).toNNReal by simp, <-NNReal.rpow_natCast] at this
        repeat
          first | rw [<-Real.toNNReal_rpow_of_nonneg (by positivity)] at this | rw [<-Real.toNNReal_add (by positivity) (by positivity)] at this | rw [<-Real.toNNReal_mul (by positivity)] at this
        rw [<-NNReal.coe_le_coe] at this
        simp [show ¬a + b + c ≤ 0 by simp; positivity, -one_div] at this
        -- Now we have a + b + c ≤ (a ^ (3 / 2) + b ^ (3 / 2) + 1) ^ (2 / 3) * (1 + 1 + c ^ 3) ^ (1 / 3).
        replace this := pow_le_pow_left₀ (by positivity) this.1 3
        rw [mul_pow] at this
        iterate 2 nth_rw 2 [<-Real.rpow_natCast] at this
        iterate 2 rw [<-Real.rpow_mul (by positivity)] at this
        norm_num at this ⊢
        nth_rw 3 [<-Real.rpow_natCast]
        exact this
  -- Return to the original goal.
  calc
    (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) ≥ (a ^ 3 + 1 + 1) * (b ^ 3 + 1 + 1) * (c ^ 3 + 1 + 1) := by
      apply mul_le_mul
      apply mul_le_mul
      pick_goal 3
      . positivity
      pick_goal 3
      . exact (show 0 ≤ a ^ 3 + 1 + 1 by positivity).trans (h₁ a ha)
      . apply h₁ a ha
      . apply h₁ b hb
      . apply h₁ c hc
      . positivity
      . apply mul_nonneg
        . exact (show 0 ≤ a ^ 3 + 1 + 1 by positivity).trans (h₁ a ha)
        . exact (show 0 ≤ b ^ 3 + 1 + 1 by positivity).trans (h₁ b hb)
    _ = (a ^ 3 + 1 + 1) * (1 + b ^ 3 + 1) * (1 + 1 + c ^ 3) := by ac_rfl
    _ ≥ (a + b + c) ^ 3 := h₃
