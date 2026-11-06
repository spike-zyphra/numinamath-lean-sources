import Mathlib
/- Find the largest possible value of the expression $\left|\sqrt{x^{2}+4 x+8}-\sqrt{x^{2}+8 x+17}\right|$ where $x$ is a real number. -/

theorem algebra_605429 : IsGreatest {y : ℝ | ∃ x, y = |√(x ^ 2 + 4 * x + 8) - √(x ^ 2 + 8 * x + 17)|} (√5):= by
    constructor
    -- Part 1: Prove that √5 belongs to the set (by showing it's achievable with x = -6)
    .
      simp
      use (-6)
      ring_nf
      rw [show √20 = √(2 ^ 2 * 5) by ring_nf]
      field_simp
      ring_nf
      have g1 : √5 ≥ 0:= by positivity
      exact Eq.symm (abs_of_nonneg g1)
    -- Part 2: Prove that √5 is an upper bound for all values in the set
    .
      simp [upperBounds]
      intro x
      -- Helper lemma 1: Triangle inequality for vectors in R²
      have h1 : ∀ x1 y1 x2 y2 : ℝ, √(x1 ^ 2 + y1 ^ 2) + √(x2 ^ 2 + y2 ^ 2) ≥ √((x1 + x2) ^ 2 + (y1 + y2) ^ 2):= by
        intro x1 y1 x2 y2
        have g1 : √(x1 ^ 2 + y1 ^ 2) + √(x2 ^ 2 + y2 ^ 2) ≥ 0:= by positivity
        rw [show √(x1 ^ 2 + y1 ^ 2) + √(x2 ^ 2 + y2 ^ 2) = √((√(x1 ^ 2 + y1 ^ 2) + √(x2 ^ 2 + y2 ^ 2)) ^ 2) by exact Eq.symm (Real.sqrt_sq g1)]
        suffices (√(x1 ^ 2 + y1 ^ 2) + √(x2 ^ 2 + y2 ^ 2)) ^ 2 ≥ (x1 + x2) ^ 2 + (y1 + y2) ^ 2 by exact Real.sqrt_le_sqrt this
        -- Expand squares and simplify
        rw [show (√(x1 ^ 2 + y1 ^ 2) + √(x2 ^ 2 + y2 ^ 2)) ^ 2 = √(x1 ^ 2 + y1 ^ 2) ^ 2 + 2 * (√(x1 ^ 2 + y1 ^ 2) * √(x2 ^ 2 + y2 ^ 2)) + √(x2 ^ 2 + y2 ^ 2) ^ 2 by ring_nf]
        have g2 : x1 ^ 2 + y1 ^ 2 ≥ 0:= by positivity
        have g3 : x2 ^ 2 + y2 ^ 2 ≥ 0:= by positivity
        rw [show √(x1 ^ 2 + y1 ^ 2) ^ 2 = x1 ^ 2 + y1 ^ 2 by exact Real.sq_sqrt g2]
        rw [show √(x2 ^ 2 + y2 ^ 2) ^ 2 = x2 ^ 2 + y2 ^ 2 by exact Real.sq_sqrt g3]
        rw [show √(x1 ^ 2 + y1 ^ 2) * √(x2 ^ 2 + y2 ^ 2) = √((x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2)) by field_simp]
        -- Prove Cauchy-Schwarz inequality
        have h1 : (x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2) ≥ (x1 * x2 + y1 * y2) ^ 2:= by
          have g4 : (x1 * y2 - x2 * y1) ^ 2 ≥ 0:= by positivity
          linarith
        replace h1 : √((x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2)) ≥ √((x1 * x2 + y1 * y2) ^ 2):= by exact Real.sqrt_le_sqrt h1
        rw [show (x1 * x2 + y1 * y2) ^ 2 = |x1 * x2 + y1 * y2| ^ 2 by exact Eq.symm (sq_abs (x1 * x2 + y1 * y2))] at h1
        have g4 : |x1 * x2 + y1 * y2| ≥ 0:= by positivity
        rw [show √(|x1 * x2 + y1 * y2| ^ 2) = |x1 * x2 + y1 * y2| by exact Real.sqrt_sq g4] at h1
        have h2 : |x1 * x2 + y1 * y2| ≥ x1 * x2 + y1 * y2:= by exact le_abs_self (x1 * x2 + y1 * y2)
        linarith
      -- Helper lemma 2: Triangle inequality for distances between points
      replace h1 : ∀ x1 y1 x2 y2 x3 y3 : ℝ, |√((x1 - x2) ^ 2 + (y1 - y2) ^ 2) - √((x1 - x3) ^ 2 + (y1 - y3) ^ 2)| ≤ √((x2 - x3) ^ 2 + (y2 - y3) ^ 2):= by
        intro x1 y1 x2 y2 x3 y3
        apply abs_le.2
        constructor
        -- Forward triangle inequality
        .
          specialize h1 (x1 - x2) (y1 - y2) (x2 - x3) (y2 - y3)
          rw [show (x1 - x2) + (x2 - x3) = x1 - x3 by ring_nf] at h1
          rw [show (y1 - y2) + (y2 - y3) = y1 - y3 by ring_nf] at h1
          linarith
        -- Reverse triangle inequality
        .
          specialize h1 (x1 - x3) (y1 - y3) (x3 - x2) (y3 - y2)
          rw [show (x1 - x3) + (x3 - x2) = x1 - x2 by ring_nf] at h1
          rw [show (y1 - y3) + (y3 - y2) = y1 - y2 by ring_nf] at h1
          rw [show (x3 - x2) ^ 2 = (x2 - x3) ^ 2 by ring_nf] at h1
          rw [show (y3 - y2) ^ 2 = (y2 - y3) ^ 2 by ring_nf] at h1
          linarith
      -- Apply the triangle inequality to specific points to prove √5 is the maximum
      specialize h1 x 0 (-2) 2 (-4) 1
      ring_nf at h1
      ring_nf
      exact h1
