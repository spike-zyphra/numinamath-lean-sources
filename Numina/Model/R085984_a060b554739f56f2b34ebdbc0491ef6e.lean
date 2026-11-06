import Mathlib

theorem algebra_236325 (a : ℝ) :
    ∃ x y, x^2 + 4 * (y - a)^2 = 4 ∧ x^2 = 2 * y ↔ a ∈ Set.Icc (-1) (17 / 8) := by 
  use Real.sqrt ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 )
  use (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4
  constructor
  · -- Assume both equations are satisfied, prove a ∈ [-1, 17/8].
    intro ⟨h₁, h₂⟩
    constructor
    · -- Prove -1 ≤ a
      nlinarith [Real.sqrt_nonneg ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 ), Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a ), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a ) ] ) ] ) ]
    · -- Prove a ≤ 17 / 8
      nlinarith [Real.sqrt_nonneg ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 ), Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a ), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a )  ]  )  ]  )  ]
  · -- Assume a ∈ [-1, 17/8], prove both equations are satisfied.
    rintro ⟨h₁, h₂⟩
    constructor
    · -- Show the first equation x^2 + 4 * (y - a) ^ 2 = 4
      nlinarith [Real.sqrt_nonneg ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 ), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 by nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a )   ]  )  ]  ), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a  )  ]  )  ]
    · -- Show the second equation x^2 = 2 * y
      nlinarith [Real.sqrt_nonneg ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2  ), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 by nlinarith [Real.sqrt_nonneg (17 - 8 * a  ), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by nlinarith [Real.sqrt_nonneg (17 - 8 * a  )  ]  )  ]  )  ]