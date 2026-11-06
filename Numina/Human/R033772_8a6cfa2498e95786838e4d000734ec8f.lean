import Mathlib

/- Let $a, b, c$ be positive real numbers. Prove that

$$
\sqrt{a^{3} b+a^{3} c}+\sqrt{b^{3} c+b^{3} a}+\sqrt{c^{3} a+c^{3} b} \geq \frac{4}{3}(a b+b c+c a)
$$ -/
theorem inequalities_605069 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (a ^ 3 * b + a ^ 3 * c) + Real.sqrt (b ^ 3 * c + b ^ 3 * a) + Real.sqrt (c ^ 3 * a + c ^ 3 * b) ≥ 4 / 3 * (a * b + b * c + c * a) := by
  -- WLOG, assume that a ≥ b.
  wlog hab : a ≥ b
  . -- Show that the other case is similar.
    simp at hab
    specialize this b a c hb ha hc (le_of_lt hab)
    ring_nf at this ⊢
    exact this
  . -- WLOG, assume that b ≥ c.
    wlog hbc : b ≥ c
    . -- Show that other cases are similar.
      simp at hbc
      by_cases hac : a ≥ c
      . specialize this a c b ha hc hb hac (le_of_lt hbc)
        ring_nf at this ⊢
        exact this
      . simp at hac
        specialize this c a b hc ha hb (le_of_lt hac) hab
        ring_nf at this ⊢
        exact this
    . -- Now we may assume that a ≥ b ≥ c.
      -- Prove the Chebyshev's inequality.
      have Chebyshev_ineq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) (h₁ : x₁ ≥ y₁) (h₂ : y₁ ≥ z₁) (h₃ : x₂ ≥ y₂) (h₄ : y₂ ≥ z₂) : x₁ * x₂ + y₁ * y₂ + z₁ * z₂ ≥ (x₁ + y₁ + z₁) * (x₂ + y₂ + z₂) / 3 := by
        nlinarith
      -- Prove the GM-HM inequality.
      have GM_HM_ineq (x y : ℝ) (hx : x > 0) (hy : y > 0) : Real.sqrt (x * y) ≥ 2 * (x * y) / (x + y) := by
        -- This is equivalent to (1 / √x - 1 / √y)² ≥ 0.
        have := sq_nonneg (1 / Real.sqrt x - 1 / Real.sqrt y)
        rw [sub_sq, div_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at this
        field_simp at this
        rw [le_div_iff₀ (by positivity)] at this
        rw [ge_iff_le, div_le_iff₀ (by positivity), Real.sqrt_mul (le_of_lt hx)]
        linarith only [this]
      -- Prove that ab ≥ ac ≥ bc.
      have h₀ : a * b ≥ a * c := by
        apply mul_le_mul_of_nonneg_left hbc (le_of_lt ha)
      have h₁ : a * c ≥ b * c := by
        apply mul_le_mul_of_nonneg_right hab (le_of_lt hc)
      -- Prove that √(ab + ac) ≥ √(bc + ba) ≥ √(ca + cb).
      have h₂ : Real.sqrt (a * b + a * c) ≥ Real.sqrt (b * c + b * a) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h₃ : Real.sqrt (b * c + b * a) ≥ Real.sqrt (c * a + c * b) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      -- Prove the goal step by step.
      calc
        Real.sqrt (a ^ 3 * b + a ^ 3 * c) + Real.sqrt (b ^ 3 * c + b ^ 3 * a) + Real.sqrt (c ^ 3 * a + c ^ 3 * b)
        _ = a * Real.sqrt (a * b + a * c) + b * Real.sqrt (b * c + b * a) + c * Real.sqrt (c * a + c * b) := by
          congrm ?_ + ?_ + ?_
          . nth_rw 3 [<-Real.sqrt_sq (le_of_lt ha)]
            rw [<-Real.sqrt_mul (by positivity)]
            ring_nf
          . nth_rw 3 [<-Real.sqrt_sq (le_of_lt hb)]
            rw [<-Real.sqrt_mul (by positivity)]
            ring_nf
          . nth_rw 3 [<-Real.sqrt_sq (le_of_lt hc)]
            rw [<-Real.sqrt_mul (by positivity)]
            ring_nf
        _ ≥ (a + b + c) * (Real.sqrt (a * b + a * c) + Real.sqrt (b * c + b * a) + Real.sqrt (c * a + c * b)) / 3 := by
          apply Chebyshev_ineq
          assumption'
        _ = (a + b + c) / 3 * (Real.sqrt (a * (b + c)) + Real.sqrt (b * (c + a)) + Real.sqrt (c * (a + b))) := by
          ring_nf
        _ ≥ (a + b + c) / 3 * (2 * (a * (b + c)) / (a + (b + c)) + 2 * (b * (c + a)) / (b + (c + a)) + 2 * (c * (a + b)) / (c + (a + b))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply add_le_add
          apply add_le_add
          . apply GM_HM_ineq a (b + c) ha (by positivity)
          . apply GM_HM_ineq b (c + a) hb (by positivity)
          . apply GM_HM_ineq c (a + b) hc (by positivity)
        _ = 4 / 3 * (a * b + b * c + c * a) := by
          rw [show a + (b + c) = a + b + c by ac_rfl, show b + (c + a) = a + b + c by ac_rfl, show c + (a + b) = a + b + c by ac_rfl]
          rw [<-add_div, <-add_div, <-mul_div_assoc, div_mul_comm, mul_div_assoc, div_self (by positivity)]
          ring
