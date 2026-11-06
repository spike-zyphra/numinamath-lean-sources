import Mathlib

open Real

theorem inequalities_135522 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) ≥ x + y + z ∧
    (x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) = x + y + z ↔ x = y ∧ y = z) := by

  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) - (x + y + z) ≥ 0 := by
    have h3 : x ^ 4 + y ^ 4 + z ^ 4 ≥ x * y * z * (x + y + z) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    have h4 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) - (x + y + z) =
        (x ^ 4 + y ^ 4 + z ^ 4 - (x + y + z) * (x * y * z)) / (x * y * z) := by 
      field_simp [show 0 < y * z by positivity, show 0 < z * x by positivity, show 0 < x * y by positivity, h1]
      ring
    rw [h4]
    have h6 : x ^ 4 + y ^ 4 + z ^ 4 - (x + y + z) * (x * y * z) ≥ 0 := by
      nlinarith [h3]
    have h7 : (x ^ 4 + y ^ 4 + z ^ 4 - (x + y + z) * (x * y * z)) / (x * y * z) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith

  constructor
  · -- First goal: prove the inequality
    linarith [h2]
  · -- Second goal: equality conditions
    constructor
    · -- Forward implication: if equality holds, then x = y ∧ y = z
      intro heq
      have h4 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) = (x ^ 4 + y ^ 4 + z ^ 4) / (x * y * z) := by
        field_simp [show 0 < y * z by positivity, show 0 < z * x by positivity, show 0 < x * y by positivity, h1]
        ring
      rw [h4] at heq
      have h5 : x ^ 4 + y ^ 4 + z ^ 4 = x * y * z * (x + y + z) := by
        field_simp [h1] at heq
        nlinarith 
      have h7 : (x - y) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2), 
          sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
        ]
      have h10 : x = y := by nlinarith 
      have h8 : (y - z) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2), 
          sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
        ]
      have h11 : y = z := by nlinarith 
      constructor 
      · -- Prove x = y 
        linarith 
      · -- Prove y = z 
        linarith 
    · -- Backward implication: if x = y ∧ y = z, then equality holds 
      rintro ⟨rfl, rfl⟩ 
      field_simp [show (0 : ℝ) < x by assumption, 
          show (0 : ℝ) < x * x by positivity, 
          show (0 : ℝ) < x * x by positivity
      ]
      <;> ring_nf <;> nlinarith