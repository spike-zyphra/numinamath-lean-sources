import Mathlib

/- Prove that for all positive real numbers $a, b$, and $c$,

$$
\frac{a^{3}}{b c}+\frac{b^{3}}{c a}+\frac{c^{3}}{a b} \geq a+b+c
$$

and determine when equality occurs.

Each of the inequalities used in the solutions below has the property that equality holds if and only if $a=b=c$. Thus equality holds for the given inequality if and only if $a=b=c$. -/

-- Main theorem: proves the inequality and characterizes the equality case
theorem algebra_604793 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) ≥ a + b + c ∧ (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) = a + b + c ↔ a = b ∧ b = c):= by
  constructor
  · -- First part: prove the inequality
    have pos1 : 0 < b * c := mul_pos hb hc
    have pos2 : 0 < c * a := mul_pos hc ha
    have pos3 : 0 < a * b := mul_pos ha hb
    have pos4 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h1 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) ≥ 0 := by
      have h2 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) =
          (a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c)) / (a * b * c) := by
        field_simp
        ring
      rw [h2]
      have h3 : a ^ 4 + b ^ 4 + c ^ 4 ≥ (a + b + c) * (a * b * c) := by
        nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
      have h4 : (a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c)) ≥ 0 := by
        linarith
      apply div_nonneg
      linarith
      positivity
    linarith
  · -- Second part: prove the equality condition
    constructor
    · -- Assume the equality holds, prove a = b = c
      intro heq
      have pos1 : 0 < b * c := mul_pos hb hc
      have pos2 : 0 < c * a := mul_pos hc ha
      have pos3 : 0 < a * b := mul_pos ha hb
      have pos4 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
      have h1 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) = 0 := by linarith [heq]
      have h2 : a ^ 4 + b ^ 4 + c ^ 4 = (a + b + c) * (a * b * c) := by
        have h3 : a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) - (a + b + c) =
            (a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c)) / (a * b * c) := by
          field_simp
          ring
        rw [h3] at h1
        have h4 : (a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c)) / (a * b * c) = 0 := by linarith [h1]
        have h5 : a ^ 4 + b ^ 4 + c ^ 4 - (a + b + c) * (a * b * c) = 0 := by
          have pos3 : a * b * c > 0 := by positivity
          field_simp at h4 ⊢
          linarith
        linarith
      have h_eq1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          pow_two_nonneg (a * b - b * c), pow_two_nonneg (b * c - c * a), pow_two_nonneg (c * a - a * b)
        ]
      have h_eq2 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          pow_two_nonneg (a * b - b * c), pow_two_nonneg (b * c - c * a), pow_two_nonneg (c * a - a * b)
        ]
      have ha1 : a - b = 0 := by
        nlinarith
      have hb1 : b - c = 0 := by
        nlinarith
      constructor
      · -- Prove a = b
        linarith
      · -- Prove b = c
        linarith
    · -- Assume a = b = c, prove the equality
      rintro ⟨ha1, hb1⟩
      have hc1 : a = c := by linarith
      rw [show b = a by linarith, show c = a by linarith]
      field_simp
      ring