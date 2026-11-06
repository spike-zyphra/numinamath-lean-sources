import Mathlib

open Real

theorem inequalities_120726 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
    (3 / 2 = a / (b + c) + b / (c + a) + c / (a + b) ↔ a = b ∧ b = c) := by
  constructor
  · -- Prove that $\frac{a}{b+c} + \frac{b}{c+a} + \frac{c}{a+b} \geq \frac{3}{2}$
    have hb' : 0 < b := hb
    have hc' : 0 < c := hc
    have ha' : 0 < a := ha
    have h1 : 0 < b + c := by linarith
    have h2 : 0 < c + a := by linarith
    have h3 : 0 < a + b := by linarith
    have h4 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
      have h6 : 0 < (b + c) * (c + a) * (a + b) := by positivity
      have h7 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
          (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      all_goals -- Apply to all goals
        positivity
    linarith
  · -- Equality holds if and only if a = b = c.
    constructor
    · -- If equality holds, then a = b = c.
      intro h
      have hb' : 0 < b := hb
      have hc' : 0 < c := hc
      have ha' : 0 < a := ha
      have h1 : 0 < b + c := by linarith
      have h2 : 0 < c + a := by linarith
      have h3 : 0 < a + b := by linarith
      have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 = 0 := by linarith 
      have h5 : (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) = 0 := by
        have h7 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
            (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
          field_simp
          ring
        rw [h7] at h4 
        linarith 
      have h7 : 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) = 0 := by 
        have eq1 : (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) = 0 := h5 
        field_simp at eq1 ⊢
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos hb ha, mul_pos hc ha, mul_pos hc hb]
      have h8 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
            sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
            sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      have h9 : a - b = 0 := by
        apply pow_eq_zero 
        exact h8 
      have h10 : a = b := by
        linarith 
      have h11 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
            sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
            sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      have h12 : b - c = 0 := by
        apply pow_eq_zero 
        exact h11
      have h13 : b = c := by
        linarith 
      constructor 
      · linarith 
      · linarith 
    · -- If a = b = c, then equality holds.
      rintro ⟨rfl, rfl⟩ 
      field_simp
      <;> nlinarith