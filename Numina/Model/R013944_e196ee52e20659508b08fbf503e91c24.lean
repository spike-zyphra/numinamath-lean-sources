import Mathlib

open Real

theorem inequalities_25700 (k : ℝ) :
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → k * a * b * c > a ^ 3 + b ^ 3 + c ^ 3 →
      (a + b > c ∧ a + c > b ∧ b + c > a)) ↔ k ≤ 5 := by
  constructor
  · -- Proof of the implication: if the statement holds, then k ≤ 5.
    intro h
    by_contra h1
    push_neg at h1
    have h2 := h 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by
      nlinarith [sq_nonneg (k - 5), h1]
    )
    norm_num at h2
  · -- Proof of the reverse implication: if k ≤ 5, then the statement holds.
    intro hk a b c ha hb hc h
    have h1 : a + b > c := by
      by_contra h2
      push_neg at h2
      have h2' : a ^ 3 + b ^ 3 + c ^ 3 ≥ 5 * a * b * c := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_nonneg (show 0 ≤ c - a - b by linarith [h2]) (show 0 ≤ c by linarith [hc])
        ]
      have h3 : k * a * b * c ≤ 5 * a * b * c := by
        have h4 : k ≤ 5 := hk
        have h5 : a * b * c > 0 := by
          apply mul_pos
          apply mul_pos
          all_goals
            linarith
        have h6 : k * (a * b * c) ≤ 5 * (a * b * c) := by
          apply mul_le_mul_of_nonneg_right
          linarith
          positivity
        linarith
      nlinarith
    have h2 : a + c > b := by
      by_contra h2
      push_neg at h2
      have h2' : a ^ 3 + b ^ 3 + c ^ 3 ≥ 5 * a * b * c := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + c - b), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_nonneg (show 0 ≤ b - a - c by linarith [h2]) (show 0 ≤ b by linarith [hb])
        ]
      have h3 : k * a * b * c ≤ 5 * a * b * c := by
        have h4 : k ≤ 5 := hk
        have h5 : a * b * c > 0 := by
          apply mul_pos
          apply mul_pos
          all_goals
            linarith
        have h6 : k * (a * b * c) ≤ 5 * (a * b * c) := by
          apply mul_le_mul_of_nonneg_right
          linarith
          positivity
        linarith
      nlinarith
    have h3 : b + c > a := by
      by_contra h2
      push_neg at h2
      have h2' : a ^ 3 + b ^ 3 + c ^ 3 ≥ 5 * a * b * c := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (b + c - a), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_nonneg (show 0 ≤ a - b - c by linarith [h2]) (show 0 ≤ a by linarith [ha])
        ]
      have h3 : k * a * b * c ≤ 5 * a * b * c := by
        have h4 : k ≤ 5 := hk
        have h5 : a * b * c > 0 := by
          apply mul_pos
          apply mul_pos
          all_goals
            linarith
        have h6 : k * (a * b * c) ≤ 5 * (a * b * c) := by
          apply mul_le_mul_of_nonneg_right
          linarith
          positivity
        linarith
      nlinarith
    exact ⟨h1, h2, h3⟩