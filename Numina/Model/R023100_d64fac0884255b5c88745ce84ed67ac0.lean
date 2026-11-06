import Mathlib

open Real Set

theorem inequalities_311342 (m : ℝ) (hm : m ∈ Icc (-sqrt 3) (sqrt 3)) :
    ∀ n : ℝ, (∀ x y z : ℝ, x^2 + 2 * y^2 + 3 * z^2 + 2 * x * y + 2 * m * z * x + 2 * n * y * z ≥ 0) ↔
    m - sqrt (3 - m^2) ≤ n ∧ n ≤ m + sqrt (3 - m^2) := by
  rcases hm with ⟨hm1, hm2⟩
  intro n
  constructor
  · -- (→) If the inequality holds for all x, y, z, then m - √(3 - m²) ≤ n ≤ m + √(3 - m²)
    intro h
    have h1 := h (-(2 * m - n) ) (m - n) 1
    have h2 : (n - m)^2 ≤ 3 - m^2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (3 - m^2), 
          sq_nonneg (m - n), sq_nonneg (1 : ℝ), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3),
          Real.sq_sqrt (show 0 ≤ (3 - m^2 : ℝ) by 
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (m : ℝ)]
          )
      ]
    constructor
    · -- m - sqrt(3 - m^2) ≤ n
      nlinarith [Real.sqrt_nonneg (3 - m^2), 
          Real.sq_sqrt (show 0 ≤ (3 - m^2 : ℝ) by 
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (m : ℝ)]
          ), 
          Real.sqrt_nonneg (3 - m^2)
      ]
    · -- n ≤ m + sqrt(3 - m^2)
      nlinarith [Real.sqrt_nonneg (3 - m^2), 
          Real.sq_sqrt (show 0 ≤ (3 - m^2 : ℝ) by 
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (m : ℝ)]
          ), 
          Real.sqrt_nonneg (3 - m^2)
      ]
  · -- (←) If m - √(3 - m²) ≤ n ≤ m + √(3 - m²), then the inequality holds for all x, y, z
    rintro ⟨h1, h2⟩
    intro x y z
    have h3 : (n - m)^2 ≤ 3 - m^2 := by
      nlinarith [Real.sqrt_nonneg (3 - m^2), 
          Real.sq_sqrt (show 0 ≤ (3 - m^2 : ℝ) by 
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (m : ℝ)]
          )
      ]
    nlinarith [sq_nonneg (x + y + m * z), sq_nonneg (y + (n - m) * z), sq_nonneg (z : ℝ), 
          Real.sqrt_nonneg (3 - m^2), 
          Real.sq_sqrt (show 0 ≤ (3 - m^2 : ℝ) by 
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (m : ℝ)]
          ), 
          h1, h2
      ]