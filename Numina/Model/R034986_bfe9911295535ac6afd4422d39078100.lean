import Mathlib


lemma lemma_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * (b - c) / (c * (a + c)) + b * (c - a) / (a * (a + b)) +
    c * (a - b) / (b * (b + c)) ≥ 0 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals
      nlinarith
  have h2 : 0 < a * (a + b) := by
    positivity
  have h3 : 0 < b * (b + c) := by
    positivity
  have h4 : 0 < c * (a + c) := by
    positivity
  have h6 : a * (b - c) / (c * (a + c)) + b * (c - a) / (a * (a + b)) + c * (a - b) / (b * (b + c)) =
    (a^2 * b * (b - c) * (a + b) * (b + c) +
    b^2 * c * (c - a) * (a + c) * (b + c) +
    c^2 * a * (a - b) * (a + b) * (a + c)) / (c * (a + c) * a * (a + b) * b * (b + c)) := by
    field_simp [show 0 < c by linarith, show 0 < a + c by positivity, show 0 < a by linarith, show 0 < a + b by positivity, show 0 < b by linarith, show 0 < b + c by positivity]
    ring
  have h7 : c * (a + c) * a * (a + b) * b * (b + c) > 0 := by positivity
  rw [h6]
  apply div_nonneg
  ·
    have h8 : a^2 * b * (b - c) * (a + b) * (b + c) +
    b^2 * c * (c - a) * (a + c) * (b + c) +
    c^2 * a * (a - b) * (a + b) * (a + c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
                mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity),
                mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity),
                mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity)
            ]
    nlinarith
  all_goals
    positivity


theorem inequalities_602024 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a * b / (c^2 + c * a) + b * c / (a^2 + a * b) + c * a / (b^2 + b * c)) ≥
    (a / (a + c) + b / (b + a) + c / (c + b)) := by
  have h1 : 0 < c^2 + c * a := by
    positivity
  have h2 : 0 < a^2 + a * b := by
    positivity
  have h3 : 0 < b^2 + b * c := by
    positivity
  have ha1 : 0 < a := by linarith
  have hb1 : 0 < b := by linarith
  have hc1 : 0 < c := by linarith
  have eq1 : a * b / (c^2 + c * a) - a / (a + c) = a * (b - c) / (c * (a + c)) := by
    field_simp [show 0 < c by positivity, show 0 < a + c by positivity, show 0 < c ^ 2 + c * a by positivity]
    <;> ring
  have eq2 : b * c / (a^2 + a * b) - b / (b + a) = b * (c - a) / (a * (a + b)) := by
    field_simp [show 0 < a by positivity, show 0 < a + b by positivity, show 0 < b + a by positivity, show 0 < a^2 + a * b by positivity]
    <;> ring
  have eq3 : (c * a / (b^2 + b * c) - c / (c + b)) = c * (a - b) / (b * (b + c)) := by
    field_simp [show 0 < b by positivity, show 0 < b + c by positivity, show 0 < c + b by positivity, show 0 < b^2 + b * c by positivity]
    <;> ring
  have eq4 : (a * b / (c^2 + c * a) + b * c / (a^2 + a * b) + c * a / (b^2 + b * c)) - (a / (a + c) + b / (b + a) + c / (c + b)) =
    a * (b - c) / (c * (a + c)) + b * (c - a) / (a * (a + b)) + c * (a - b) / (b * (b + c)) := by
    have h17 : (a * b / (c^2 + c * a) + b * c / (a^2 + a * b) + c * a / (b^2 + b * c)) - (a / (a + c) + b / (b + a) + c / (c + b)) =
        (a * b / (c^2 + c * a) - a / (a + c)) + (b * c / (a^2 + a * b) - b / (b + a)) + (c * a / (b^2 + b * c) - c / (c + b)) := by
      ring
    rw [h17]
    rw [eq1, eq2, eq3]
  have h7 : a * (b - c) / (c * (a + c)) + b * (c - a) / (a * (a + b)) + c * (a - b) / (b * (b + c)) ≥ 0 := by
    apply lemma_1 a b c ha hb hc
  linarith [eq4, h7]