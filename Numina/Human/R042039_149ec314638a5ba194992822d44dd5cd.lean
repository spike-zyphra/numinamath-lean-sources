import Mathlib

/-Find the smallest positive real number $a$ so that the polynomial
\[x^6 + 3ax^5 + (3a^2 + 3) x^4 + (a^3 + 6a) x^3 + (3a^2 + 3) x^2 + 3ax + 1 = 0\]has at least one real root.-/
theorem algebra_18671 : 
    IsLeast {a : ℝ | 0 < a ∧ ∃ x : ℝ, x ^ 6 + 3 * a * x ^ 5 + (3 * a ^ 2 + 3) * x ^ 4 + (a ^ 3 + 6 * a) * x ^ 3 + (3 * a ^ 2 + 3) * x ^ 2 + 3 * a * x + 1 = 0} 2 := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  -- show 2 is a lower bound
  . use (-1)
    ring_nf
  -- show the main part of the conclusion
  . intro a ha x hx
    -- show that x ≠ 0
    have hx0 : x ≠ 0 := by
      contrapose! hx
      rw [hx]
      norm_num
    -- dividing the equation by x^3 and simplifying
    replace hx : x ^ 3 + 1 / x ^ 3 + 3 * a * (x ^ 2 + 1 / x ^ 2) + (3 * a ^ 2 + 3) * (x + 1 / x) + (a ^ 3 + 6 * a) = 0 := by
      field_simp
      ring_nf
      calc x ^ 3 + x ^ 4 * a * 3 + x ^ 5 * 3 + x ^ 5 * a ^ 2 * 3 + x ^ 6 * a * 6 + x ^ 6 * a ^ 3 + x ^ 7 * 3 + x ^ 7 * a ^ 2 * 3 + x ^ 8 * a * 3 + x ^ 9
          = x ^ 3 * (x ^ 6 + 3 * a * x ^ 5 + (3 * a ^ 2 + 3) * x ^ 4 + (a ^ 3 + 6 * a) * x ^ 3 + (3 * a ^ 2 + 3) * x ^ 2 + 3 * a * x + 1) := by ring_nf
        _ = 0 := by rw [hx]; norm_num
    
    -- set y := x + 1 / x
    set y := x + 1 / x with hy1
    -- show that x ^ 2 + 1 / x ^ 2 = y ^ 2 - 2
    have hy2 : x ^ 2 + 1 / x ^ 2 = y ^ 2 - 2 := by
      rw [hy1]
      field_simp
      ring_nf
    -- show that x ^ 3 + 1 / x ^ 3 = y ^ 3 - 3y
    have hy3 : x ^ 3 + 1 / x ^ 3 = y ^ 3 - 3 * y := by
      rw [hy1]
      field_simp
      ring_nf
    -- substitute to hx
    rw [hy2, hy3] at hx
    -- simplify to (y + a) ^ 3 = 0
    have hy : (y + a) ^ 3 = 0 := by
      ring_nf at hx ⊢
      exact hx
    -- show that y + a = 0
    have h1 : y + a = 0 := by
      contrapose! hy
      apply pow_ne_zero
      exact hy
    -- show that x < 0， proof by contradiction
    replace hx0 : x < 0 := by
      contrapose! h1
      -- show that 0 < y
      replace hy : 0 < y := by
        rw [hy1]
        positivity
      linarith only [hy, ha]
    
    -- have lemma of am-gm inequality
    have lm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : √(4 * a * b) ≤ a + b := by
      rw [@Real.sqrt_le_left]
      linarith only [show 0 ≤ (a - b) ^ 2 by positivity]
      linarith only [ha, hb]
    -- finally calculate that a ≥ 2
    calc 
      2 = √(2 ^ 2) := by rw [Real.sqrt_sq]; norm_num
      _ = √(4 * (x * (1 / x))) := by rw [mul_div_cancel₀]; ring_nf; linarith only [hx0]
      _ = √(4 * (-x) * (1 / (-x))) := by ring_nf
      -- use lemma of am-gm inequality
      _ ≤ (-x) + 1 / (-x) := by apply lm (-x) (1 / (-x)); linarith only [hx0]; apply div_pos; norm_num; linarith only [hx0]
      _ = - (x + 1 / x) := by ring_nf
      _ = - y := by rw [hy1]
      _ = a := by linear_combination -h1