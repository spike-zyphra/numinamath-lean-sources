import Mathlib

open Real

theorem inequalities_144762 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 ∧
    (a / (b + c) + b / (a + c) + c / (a + b) = 3 / 2 ↔ a = b ∧ b = c) := by
  constructor
  · -- Prove a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2
    have ha1 : 0 < a := ha
    have hb1 : 0 < b := hb
    have hc1 : 0 < c := hc
    have pos1 : 0 < b + c := by linarith
    have pos2 : 0 < a + c := by linarith
    have pos3 : 0 < a + b := by linarith
    have h : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
      have h1 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
        (2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b)) / (2 * (b + c) * (a + c) * (a + b)) := by
        field_simp
        ring
      rw [h1] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      all_goals
        positivity
    linarith
  · -- Prove the equality condition
    constructor
    · -- Forward: if a/(b+c)+b/(a+c)+c/(a+b)=3/2, then a = b and b = c
      intro heq
      have ha1 : 0 < a := ha
      have hb1 : 0 < b := hb
      have hc1 : 0 < c := hc
      have pos1 : 0 < b + c := by linarith
      have pos2 : 0 < a + c := by linarith
      have pos3 : 0 < a + b := by linarith
      have heq1 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 = 0 := by linarith [heq]
      have h1 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
        (2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b)) / (2 * (b + c) * (a + c) * (a + b)) := by
        field_simp
        ring
      rw [h1] at heq1
      have heq2 : (2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b)) = 0 := by
        field_simp at heq1 ⊢
        linarith
      have h2 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      have h3 : (a - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      have h11 : a - b = 0 := by
        rw [sq_eq_zero_iff] at h2
        linarith
      have h12 : a - c = 0 := by
        rw [sq_eq_zero_iff] at h3
        linarith
      constructor
      · -- Show a = b
        linarith
      · -- Show b = c
        linarith
    · -- Backward: if a = b and b = c, then a/(b+c)+b/(a+c)+c/(a+b)=3/2
      rintro ⟨ha1, hb1⟩
      have ha2 : a = c := by
        linarith
      rw [show b = a by linarith [ha1], show c = a by linarith [ha2]]
      field_simp
      <;> nlinarith