import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_320720
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b > c)
    (h' : a + c > b)
    (h'' : b + c > a) :
    b^2 * c * (b - c) + c^2 * a * (c - a) +
    a^2 * b * (a - b) ≥ 0 ∧
    (b^2 * c * (b - c) + c^2 * a * (c - a) +
     a^2 * b * (a - b) = 0 ↔
     (a = b ∧ b = c)) := by

  constructor
  · -- Prove the inequality b^2 * c * (b - c) + c^2 * a * (c - a) + a^2 * b * (a - b) ≥ 0
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), 
          sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), 
          sq_nonneg (c * (b - c)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
        ]
  · -- Prove if the inequality is equal to 0 if and only if a = b ∧ b = c
    constructor
    · -- Forward direction: if b^2 * c * (b - c) + c^2 * a * (c - a) + a^2 * b * (a - b) = 0, then (a = b ∧ b = c)
      intro heq
      have h1 : (a - b) ^ 2 = 0 := by 
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (a * (b - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), 
          sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), 
          sq_nonneg (c * (b - c))
        ]
      have h2 : a - b = 0 := by
        apply pow_eq_zero 
        exact h1
      have h3 : a = b := by linarith
      have h4 : (b - c) ^ 2 = 0 := by
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
          h3, sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c))
        ]
      have h5 : b - c = 0 := by
        apply pow_eq_zero 
        exact h4
      have h6 : b = c := by linarith
      exact ⟨h3, h6⟩
    · -- Backward direction: if (a = b ∧ b = c), then b^2 * c * (b - c) + c^2 * a * (c - a) + a^2 * b * (a - b) = 0
      rintro ⟨rfl, rfl⟩
      all_goals 
        ring_nf