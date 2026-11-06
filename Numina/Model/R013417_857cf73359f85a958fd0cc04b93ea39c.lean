import Mathlib

open Real

theorem inequalities_292476 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c) ∧
    (2 / (a + b) + 2 / (b + c) + 2 / (c + a) = 9 / (a + b + c) ↔ a = b ∧ b = c) := by
  constructor
  · -- First part: proving the inequality.
    have h1 : 0 < a + b := by linarith
    have h2 : 0 < b + c := by linarith
    have h3 : 0 < c + a := by linarith
    have h4 : 0 < a + b + c := by linarith
    have h5 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) ≥ 0 := by
      have h6 : 0 < (a + b) * (b + c) * (c + a) * (a + b + c) := by positivity
      have h7 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) =
          (2 * (b + c) * (c + a) * (a + b + c) + 2 * (a + b) * (c + a) * (a + b + c) + 2 * (a + b) * (b + c) * (a + b + c) - 9 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a) * (a + b + c)) := by 
        field_simp
        <;> ring
      rw [h7]
      apply div_nonneg
      · -- Prove numerator non-negative.
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - (a + b)), sq_nonneg (a + b + c - (b + c)), sq_nonneg (a + b + c - (c + a)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a + b from by linarith) (show 0 < a + b + c from by linarith),
          mul_pos (show 0 < b + c from by linarith) (show 0 < a + b + c from by linarith),
          mul_pos (show 0 < c + a from by linarith) (show 0 < a + b + c from by linarith)
        ]
      · -- Prove denominator positive.
        positivity
    linarith
    <;> try positivity
    <;> try { linarith }
  · -- Second part: equality holds iff a = b ∧ b = c.
    constructor
    · -- Assume equality holds.
      intro heq 
      have h1 : 0 < a + b := by linarith
      have h2 : 0 < b + c := by linarith
      have h3 : 0 < c + a := by linarith
      have h4 : 0 < a + b + c := by linarith 
      have h6 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) = 0 := by linarith 
      have h7 : 2 * (b + c) * (c + a) * (a + b + c) + 2 * (a + b) * (c + a) * (a + b + c) + 2 * (a + b) * (b + c) * (a + b + c) - 9 * (a + b) * (b + c) * (c + a) = 0 := by
        have h6' : 0 < (a + b) * (b + c) * (c + a) * (a + b + c) := by positivity 
        have h7 : (2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c)) =
            (2 * (b + c) * (c + a) * (a + b + c) + 2 * (a + b) * (c + a) * (a + b + c) + 2 * (a + b) * (b + c) * (a + b + c) - 9 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a) * (a + b + c)) := by 
          field_simp
          <;> ring
        rw [h7] at h6 
        field_simp at h6 ⊢
        <;> nlinarith 
      have h8 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b from by linarith) (show 0 < a + b + c from by linarith),
          mul_pos (show 0 < b + c from by linarith) (show 0 < a + b + c from by linarith),
          mul_pos (show 0 < c + a from by linarith) (show 0 < a + b + c from by linarith)
        ]
      have h9 : a - b = 0 := by
        nlinarith
      have h10 : a = b := by linarith
      -- Similarly for the other square
      have h11 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b from by linarith) (show 0 < a + b + c from by linarith),
          mul_pos (show 0 < b + c from by linarith) (show 0 < a + b + c from by linarith),
          mul_pos (show 0 < c + a from by linarith) (show 0 < a + b + c from by linarith)
        ]
      have h12 : b - c = 0 := by
        nlinarith
      have h13 : b = c := by linarith
      exact ⟨h10, h13⟩
    · -- Show that a = b ∧ b = c implies equality.
      rintro ⟨rha, rhb⟩
      have h1 : a = b := by
        exact rha
      have h2 : b = c := by
        exact rhb
      have h3 : a = c := by
        linarith [h1, h2]
      have h4 : 0 < a + b := by linarith
      have h5 : 0 < b + c := by linarith
      have h6 : 0 < c + a := by linarith
      have h7 : 0 < a + b + c := by linarith
      field_simp
      <;> ring_nf <;> simp [h1, h2, h3] <;> linarith