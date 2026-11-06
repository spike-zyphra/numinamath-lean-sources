import Mathlib

theorem inequalities_86116 :
    (∀ x y : ℝ, x > 0 → y > 0 → x / y ^ 2 + y / x ^ 2 ≥ 1 / x + 1 / y) ∧
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → (a + b) / c ^ 2 + (b + c) / a ^ 2 + (c + a) / b ^ 2 ≥
      2 * (1 / a + 1 / b + 1 / c)) := by
  constructor
  · -- Proof of a
    intro x y hx hy
    have h1 : x / y^2 + y / x^2 - (1 / x + 1 / y) ≥ 0 := by
      have h2 : x / y^2 + y / x^2 - (1 / x + 1 / y) = (x^3 + y^3 - (x * y^2 + y * x^2)) / (x^2 * y^2) := by
        field_simp
        ring
      rw [h2]
      have h3 : x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2) ≥ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2)]
      have h4 : (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  · -- Proof of b
    intro a b c ha hb hc
    have h1 : a / b^2 + b / a^2 ≥ 1 / a + 1 / b := by 
      have h41 : ∀ x y : ℝ, x > 0 → y > 0 → x / y ^ 2 + y / x ^ 2 ≥ 1 / x + 1 / y := by
        intro x y hx hy
        have h141 : x / y ^ 2 + y / x ^ 2 - (1 / x + 1 / y) ≥ 0 := by
          have h2 : x / y ^ 2 + y / x ^ 2 - (1 / x + 1 / y) = (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) := by
            field_simp
            ring
          rw [h2]
          have h31414 : x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2) ≥ 0 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2)]
          have h41414 : (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) ≥ 0 := by
            apply div_nonneg
            linarith
            positivity
          linarith
        linarith
      specialize h41 a b ha hb
      linarith
    have h11 : b / c^2 + c / b^2 ≥ 1 / b + 1 / c := by 
      have h4111 : ∀ x y : ℝ, x > 0 → y > 0 → x / y ^ 2 + y / x ^ 2 ≥ 1 / x + 1 / y := by
        intro x y hx hy
        have h141 : x / y ^ 2 + y / x ^ 2 - (1 / x + 1 / y) ≥ 0 := by
          have h2 : x / y ^ 2 + y / x ^ 2 - (1 / x + 1 / y) = (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) := by
            field_simp
            ring
          rw [h2]
          have h31414 : x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2) ≥ 0 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2)]
          have h41414 : (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) ≥ 0 := by
            apply div_nonneg
            linarith
            positivity
          linarith
        linarith
      specialize h4111 b c hb hc
      linarith
    have h22 : c / a^2 + a / c^2 ≥ 1 / c + 1 / a := by 
      have h42 : ∀ x y : ℝ, x > 0 → y > 0 → x / y ^ 2 + y / x ^ 2 ≥ 1 / x + 1 / y := by
        intro x y hx hy
        have h17141 : x / y ^ 2 + y / x ^ 2 - (1 / x + 1 / y) ≥ 0 := by
          have h2 : x / y ^ 2 + y / x ^ 2 - (1 / x + 1 / y) = (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) := by
            field_simp
            ring
          rw [h2]
          have h3171414 : x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2) ≥ 0 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2)]
          have h4171414 : (x ^ 3 + y ^ 3 - (x * y ^ 2 + y * x ^ 2)) / (x ^ 2 * y ^ 2) ≥ 0 := by
            apply div_nonneg
            linarith
            positivity
          linarith
        linarith
      specialize h42 c a hc ha
      linarith 
    have h51211 : a / b ^ 2 + b / a ^ 2 + (b / c ^ 2 + c / b ^ 2) + (c / a ^ 2 + a / c ^ 2) ≥ 2 * (1 / a + 1 / b + 1 / c) := by 
      linarith [h1, h11, h22]
    have h6 : (a + b) / c^2 + (b + c) / a^2 + (c + a) / b^2 = a / b ^ 2 + b / a ^ 2 + (b / c ^ 2 + c / b ^ 2) + (c / a ^ 2 + a / c ^ 2) := by
      field_simp
      <;> 
      ring
    rw [h6] at *
    linarith