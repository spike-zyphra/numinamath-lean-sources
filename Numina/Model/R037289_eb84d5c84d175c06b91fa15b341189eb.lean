import Mathlib

open Real

theorem inequalities_260268 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / c + c / b ≥ 4 * a / (a + b) ∧
    (a / c + c / b = 4 * a / (a + b) ↔ a = c ∧ b = c) := by
  constructor
  · -- Prove the inequality $\frac{a}{c}+\frac{c}{b}\geq \frac{4 a}{a+b}$
    have h1 : 0 < b * c * (a + b) := by
      positivity
    have h2 : a / c + c / b - 4 * a / (a + b) ≥ 0 := by
      have h3 : a / c + c / b - 4 * a / (a + b) =
          (a * b * (a + b) + c ^ 2 * (a + b) - 4 * a * c * b) / (c * b * (a + b)) := by
        field_simp
        ring
      rw [h3] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (c - a), sq_nonneg (c - b), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a + b from by linarith) hc, mul_pos (show 0 < a + b from by linarith) hb, mul_pos (show 0 < a + b from by linarith) ha
      ]
      all_goals
        positivity
    linarith
  · -- Now prove the equality condition
    constructor
    · -- Assume equality holds, prove a = c ∧ b = c
      intro heq
      have h1 : 0 < b * c * (a + b) := by
        positivity
      have eq1 : a * b * (a + b) + c ^ 2 * (a + b) - 4 * a * c * b = 0 := by
        have he1 : a / c + c / b - 4 * a / (a + b) = 0 := by
          linarith
        have h3 : a / c + c / b - 4 * a / (a + b) =
            (a * b * (a + b) + c ^ 2 * (a + b) - 4 * a * c * b) / (c * b * (a + b)) := by
          field_simp
          ring
        rw [h3] at he1
        field_simp at he1 ⊢
        nlinarith
      -- Now we need to prove `a = c` and `b = c` from `eq1`.
      have eq3 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (c - (a + b) / 2), sq_nonneg (c * (a + b) - 2 * a * b), sq_nonneg (a - b), sq_nonneg (c - a), sq_nonneg (c - b),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a + b by linarith) ha, mul_pos (show 0 < a + b by linarith) hb, mul_pos (show 0 < a + b by linarith) hc
        ]
      have eq4 : a - b = 0 := by
        nlinarith
      have eq5 : a = b := by
        linarith
      -- Now prove c = a
      have eq6 : c = a := by
        rw [show b = a by linarith [eq5]] at eq1
        have eq7 : (a - c) ^ 2 = 0 := by
          nlinarith [sq_nonneg (a - c)]
        have eq8 : a - c = 0 := by
          nlinarith
        have eq9 : a = c := by
          linarith
        linarith
      -- Now prove `a = c` and `b = c`
      have eq7 : a = c := by 
        linarith [eq6]
      have eq8 : b = c := by
        linarith [eq5, eq7]
      exact ⟨eq7, eq8⟩
    · -- Assume the conditions hold, prove equality
      rintro ⟨h1, h2⟩
      have h3 : a = c := by
        linarith
      have h4 : b = c := by
        linarith
      rw [show c = a by linarith [h3], show b = a by linarith [show b = a by linarith [h4, h3]]]
      field_simp
      <;> ring