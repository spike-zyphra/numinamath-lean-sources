import Mathlib

theorem inequalities_166404 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) ≥ 0 ∧
    ((a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) = 0 ↔
      (a = b ∧ b = c)) := by
  constructor
  · -- First part: inequality ≥ 0
    have h1 : (a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) ≥ 0 := by
      have h2 : 0 < (b + c) * (c + a) * (a + b) := by positivity
      have h3 : (a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) - 0 ≥ 0 := by
        have h4 : (a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) - 0 =
            ((a + b - 2 * c) * (c + a) * (a + b) + (b + c - 2 * a) * (b + c) * (a + b) + (c + a - 2 * b) * (b + c) * (c + a)) / ((b + c) * (c + a) * (a + b)) := by
          field_simp
          <;> ring
        rw [h4] at *
        apply div_nonneg
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        positivity
      linarith
    linarith
  · -- Second part: equality holds ↔ a = b and b = c
    constructor
    · -- Forward implication: equality implies a = b and b = c
      intro heq
      have h9 : 0 < (b + c) * (c + a) * (a + b) := by positivity
      -- Transform the equation to clear denominators
      have eq1 : (a + b - 2 * c) * (c + a) * (a + b) + (b + c - 2 * a) * (b + c) * (a + b) + (c + a - 2 * b) * (b + c) * (c + a) = 0 := by
        have eq2 : (a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) = 0 := by linarith
        have eq3 : ((a + b - 2 * c) * (c + a) * (a + b) + (b + c - 2 * a) * (b + c) * (a + b) + (c + a - 2 * b) * (b + c) * (c + a)) / ((b + c) * (c + a) * (a + b)) = 0 := by
          have eq4 : (a + b - 2 * c) / (b + c) + (b + c - 2 * a) / (c + a) + (c + a - 2 * b) / (a + b) =
              ((a + b - 2 * c) * (c + a) * (a + b) + (b + c - 2 * a) * (b + c) * (a + b) + (c + a - 2 * b) * (b + c) * (c + a)) / ((b + c) * (c + a) * (a + b)) := by
            field_simp
            <;> ring
          nlinarith [eq2, eq4]
        have eq4 : (a + b - 2 * c) * (c + a) * (a + b) + (b + c - 2 * a) * (b + c) * (a + b) + (c + a - 2 * b) * (b + c) * (c + a) = 0 := by
          field_simp at eq3
          nlinarith
        exact eq4
      have eq2 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b))]
      -- Prove a = b
      have eq3 : a - b = 0 := by 
        nlinarith
      have eq4 : a = b := by linarith
      -- Prove b = c
      have eq5 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b))]
      have eq6 : b - c = 0 := by 
        nlinarith
      have eq7 : b = c := by linarith
      constructor
      · linarith
      · linarith
    · -- Backward implication: a = b and b = c implies equality
      rintro ⟨rha, rhb⟩
      rw [show b = a by linarith [rha], show c = a by linarith [rha, rhb]]
      have h2 : 0 < a := by assumption
      field_simp
      <;> nlinarith