import Mathlib

open Polynomial

/-

The equation


$$

\left(x^{2}+a x+b\right)\left(x^{2}+a x+c\right)=0

$$


has four distinct real solutions, which are $a, b, c$ and $-1$. Determine the numbers $a, b$, and $c$. -/
theorem algebra_208659 (a b c : ℝ) (h : a ≠ b ∧ a ≠ c ∧ a ≠ -1 ∧ b ≠ c ∧ b ≠ -1 ∧ c ≠ -1)
    : ((X^2 + C a * X + C b) * (X^2 + C a * X + C c)) = (X - C a) * (X - C b) * (X - C c) * (X - C (-1))↔
    a = 1 ∧ b = -2 ∧ c = 0 ∨ a = 1 ∧ b = 0 ∧ c = -2 ∨
    a = 1 / 2 ∧ b = -1 / 2 ∧ c = 0 ∨ a = 1 / 2 ∧ b = 0 ∧ c = -1 / 2 := by
  obtain ⟨hab, hac, ha_neg_one, hbc, hb_neg_one, hc_neg_one⟩ := h
  constructor
  -- proving equality implies a, b, c values
  . rintro h
    -- multiply and equate 3rd coefficient to find following
    have h_sum : -2 * a = a + b + c - 1 := by
      ring_nf at h
      replace h := congrArg (fun (p : ℝ[X]) ↦ p.coeff 3) h
      simp at h
      rw [Polynomial.coeff_X_pow_mul'] at h
      repeat rw [Polynomial.coeff_mul_X_pow'] at h
      simp at h
      rw [← C_pow, coeff_C_ne_zero (by norm_num) ] at h
      linarith
    -- multiply and equate 0th coefficient to find following
    have h_prod : (a + 1) * b * c = 0 := by
      ring_nf at h
      replace h := congrArg (fun (p : ℝ[X]) ↦ p.coeff 0) h
      simp at h
      linarith
    -- a + 1 ≠ 0 due to a ≠ -1
    have : a + 1 ≠ 0 := by
      by_contra ha
      have : a = -1 := by linarith
      contradiction
    -- so b = 0 or c = 0
    simp [this] at h_prod
    -- wlog b = 0 as otherwise it's symmetric for c = 0
    wlog hb : b = 0 generalizing b c
    . simp [hb] at h_prod
      specialize this c b hac hab hbc.symm hc_neg_one hb_neg_one (by linear_combination h) (by linarith) (by left; assumption) h_prod
      revert this
      tauto
    simp [hb]
    norm_num
    rw [hb] at h_sum
    -- write c in terms of a
    replace h_sum : c = 1 - 3 * a := by linarith
    -- evaluate the polynomials at a
    replace h := congrArg (fun p ↦ p.eval a) h
    simp at h
    rw [hb] at hab h
    ring_nf at h
    -- as a^2 * 2 ≠ 0 we get a quadratic eqn of a, which gives us a = 1/2 or a = 1
    have : a^2 * 2 ≠ 0 := by simpa
    simp [this] at h
    replace h : (2 * a - 1) * (a - 1) = 0 := by linarith
    simp at h
    obtain h | h := h
    -- these give us the two different solution
    . right
      and_intros <;> linarith
    . left
      and_intros <;> linarith
  -- to prove values imply equality of polynomial
  . rintro h
    obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := h
    all_goals simp
    -- for first two we just convert C 2 to 2 and work use ring
    . rw [show C (2 : ℝ) = 2 by norm_cast]
      ring
    . rw [show C (2 : ℝ) = 2 by norm_cast]
      ring
    -- for last two, we actually have to equate the expressions by hand as C of rationals can't be handled by ring
    . ring_nf
      calc
        _ = X * C (1 / 2 : ℝ) * C (-1 / 2) + (X ^ 2 * C (1 / 2) ^ 2 + X ^ 2 * C (-1 / 2)) + X ^ 3 * C (1 / 2) * 2 + X ^ 4  := by ring
        _ = X * C (1/2 * (-1/2)) + X^2 * C (1/4 - 1/2) + X^3 + X^4 := by
          congr 2
          . congr 1
            . rw [mul_assoc, C_mul]
            . rw [← mul_add, ← C_pow, ← C_add]
              ring_nf
          . rw [show (2 : ℝ[X]) = C 2 by norm_cast, mul_assoc, ← C_mul]
            norm_num
        _ = X * C (1 / 2) * C (-1 / 2) + (X ^ 2 * - C (1 / 2) + X ^ 2 * C (1 / 2) * C (-1 / 2) + X ^ 2 * -C (-1 / 2)) + (X ^ 3 + X ^ 3 * -C (1 / 2) + X ^ 3 * -C (-1 / 2)) + X ^ 4 := by
          congr 2
          . congr 1
            . rw [mul_assoc, C_mul]
            . rw [mul_assoc, ← mul_add, ← mul_add, ← C_mul, ← C_neg, ← C_neg, ← C_add, ← C_add]
              ring_nf
          . rw [add_assoc, ← mul_add, ← neg_add, ← C_add]
            ring_nf
            simp
        _ = _ := by ring
    . ring_nf
      calc
        _ = X * (C (1 / 2 : ℝ) * C (-1 / 2)) + X ^ 2 * (C (1 / 2) ^ 2 + C (-1 / 2)) + X ^ 3 * (C (1 / 2) * 2) + X ^ 4 := by ring
        _ = X * (C (1 / 2) * C (-1 / 2)) + X ^ 2 * (- C (1 / 2) + C (1 / 2) * C (-1 / 2) - C (-1 / 2)) + X ^ 3 * (1 - C (1 / 2) - C (-1 / 2)) + X ^ 4 := by
          congr 2
          . congr 2
            rw [← C_mul, ← C_neg, ← C_pow, ← C_add, ← C_add, ← C_sub]
            ring_nf
          . rw [show (2 : ℝ[X]) = C 2 by norm_cast, ← C_mul, sub_sub, ← C_add]
            ring_nf
            simp
        _ = _ := by ring