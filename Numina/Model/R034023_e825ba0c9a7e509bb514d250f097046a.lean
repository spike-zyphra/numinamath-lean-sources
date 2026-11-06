import Mathlib

theorem inequalities_164355 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) +
    (c ^ 2 + a ^ 2) / (2 * b) ∧
    (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) +
    (c ^ 2 + a ^ 2) / (2 * b) ≤ (a ^ 3) / (b * c) + (b ^ 3) / (c * a) +
    (c ^ 3) / (a * b) := by
  constructor
  · -- Prove the left inequality: $a + b + c \leq \frac{a^2+b^2}{2c}+\frac{b^2+c^2}{2a}+\frac{c^2+a^2}{2b}$
    have h1 : 0 < a * b * c := by apply mul_pos; apply mul_pos ha hb; exact hc
    have h2 : 0 < 2 * a * b * c := by nlinarith
    have h3 : a + b + c ≤ (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) +
        (c ^ 2 + a ^ 2) / (2 * b) := by
      have h4 : 0 < a * b * c := h1
      have h5 : 0 < 2 * a * b * c := h2
      have h6 : a + b + c - ((a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) +
          (c ^ 2 + a ^ 2) / (2 * b)) ≤ 0 := by
        have h7 : 0 < (2 * a * b * c) := h2
        have h10 : (a + b + c - ((a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) +
            (c ^ 2 + a ^ 2) / (2 * b)) ) = ( (2 * a^2 * b * c ) + (2 * a * b^2 * c ) + (2 * a * b * c^2 ) - ( a^3 * b + a * b^3 ) - (b^3 * c + b * c^3 ) - (c^3 * a + a^3 * c ) ) / (2 * a * b * c ) := by
          field_simp
          ring
        rw [h10] at *
        have h11 : (2 * a^2 * b * c ) + (2 * a * b^2 * c ) + (2 * a * b * c^2 ) - ( a^3 * b + a * b^3 ) - (b^3 * c + b * c^3 ) - (c^3 * a + a^3 * c ) ≤ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), sq_nonneg (b * (b - a) ), sq_nonneg (b * (b - c) ), sq_nonneg (c * (c - a) ), sq_nonneg (c * (c - b) ), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
        have h12 : ( (2 * a^2 * b * c ) + (2 * a * b^2 * c ) + (2 * a * b * c^2 ) - ( a^3 * b + a * b^3 ) - (b^3 * c + b * c^3 ) - (c^3 * a + a^3 * c ) ) / (2 * a * b * c ) ≤ (0 : ℝ) := by
          apply div_nonpos_of_nonpos_of_nonneg
          · linarith [h11]
          · positivity
        linarith
      linarith
    linarith
  · -- Prove the right inequality: $\frac{a^2+b^2}{2c}+\frac{b^2+c^2}{2a}+\frac{c^2+a^2}{2b} \leq \frac{a^3}{bc}+\frac{b^3}{ca}+\frac{c^3}{ab}$
    have h1 : 0 < a * b * c := by apply mul_pos; apply mul_pos ha hb; exact hc
    have h2 : 0 < 2 * a * b * c := by nlinarith
    have h6 : (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ≤ (a ^ 3) / (b * c) + (b ^ 3) / (c * a) + (c ^ 3) / (a * b) := by
      have h4 : 0 < a * b * c := h1
      have h5 : 0 < 2 * a * b * c := h2
      have h13 : (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) - ( (a ^ 3) / (b * c) + (b ^ 3) / (c * a) + (c ^ 3) / (a * b) ) ≤ 0 := by
        have h7 : 0 < (2 * a * b * c) := h2
        have h18 : ( (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) - ( (a ^ 3) / (b * c) + (b ^ 3) / (c * a) + (c ^ 3) / (a * b) ) ) =
            ( (a^3 * b + a * b^3 + b^3 * c + b * c^3 + c^3 * a + a^3 * c ) - (2 * a^4 + 2 * b^4 + 2 * c^4 ) ) / (2 * a * b * c ) := by
          field_simp
          ring
        rw [h18] at *
        have h19 : (a^3 * b + a * b^3 + b^3 * c + b * c^3 + c^3 * a + a^3 * c ) - (2 * a^4 + 2 * b^4 + 2 * c^4 ) ≤ 0 := by
          nlinarith [sq_nonneg (a^2 - b^2 ), sq_nonneg (b^2 - c^2 ), sq_nonneg (c^2 - a^2 ), 
            sq_nonneg (a - b ), sq_nonneg (b - c ), sq_nonneg (c - a ), 
            sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), 
            sq_nonneg (b * (b - a) ), sq_nonneg (b * (b - c) ), 
            sq_nonneg (c * (c - a) ), sq_nonneg (c * (c - b) ), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            sq_nonneg (a* b - b * c ), sq_nonneg (b * c - a * c ), sq_nonneg (b * c - b * a ), 
            sq_nonneg (a^2 * b - a * b^2 ), sq_nonneg (a^2 * b - a^2 * c ), sq_nonneg (a^2 * c - a * c^2 ), 
            sq_nonneg (a * b^2 - a * c^2 ), sq_nonneg (a * c^2 - b^2 * c ), sq_nonneg (b^2 * c - a^2 * b )
            ]
        have h20 : ( (a^3 * b + a * b^3 + b^3 * c + b * c^3 + c^3 * a + a^3 * c ) - (2 * a^4 + 2 * b^4 + 2 * c^4 ) ) / (2 * a * b * c ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith [h19]
          · positivity
        linarith
      linarith
    linarith