import Mathlib
/- The curves $x^{2}+y^{2}=36$ and $y=x^{2}-7$ intersect at four points. Find the sum of the squares of the $x$-coordinates of these points. -/
theorem algebra_608593 (x1 x2 x3 x4 y1 y2 y3 y4: ℝ) (h : x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4) (h1 : y1 = x1 ^ 2 - 7 ∧ y2 = x2 ^ 2 - 7 ∧ y3 = x3 ^ 2 - 7 ∧ y4 = x4 ^ 2 - 7) (h2 : x1 ^ 2 + y1 ^ 2 = 36 ∧ x2 ^ 2 + y2 ^ 2 = 36 ∧ x3 ^ 2 + y3 ^ 2 = 36 ∧ x4 ^ 2 + y4 ^ 2 = 36) : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 = 26:= by

-- Destructure the hypotheses for easier access
  rcases h with ⟨g1, g2, g3, g4, g5, g6⟩
  rcases h2 with ⟨h5, h6, h7, h8⟩
  rcases h1 with ⟨h1, h2, h3, h4⟩

-- Key step: Prove that sum of y-coordinates equals -2
  suffices y1 + y2 + y3 + y4 = -2 by linarith

-- Transform equations into quadratic form in y
  replace h5 : y1 ^ 2 + y1 - 29 = 0:= by linarith
  replace h6 : y2 ^ 2 + y2 - 29 = 0:= by linarith
  replace h7 : y3 ^ 2 + y3 - 29 = 0:= by linarith
  replace h8 : y4 ^ 2 + y4 - 29 = 0:= by linarith

-- Helper lemma: If x ≠ y and they give same y-coordinate, then x + y = 0
  have h9 : ∀ x y : ℝ, x ≠ y → x ^ 2 - 7 = y ^ 2 - 7 → x + y = 0:= by
    intro x y hxy h
    replace h : (x + y) * (x - y) = 0:= by linarith
    replace hxy : x - y ≠ 0:= by exact sub_ne_zero_of_ne hxy
    simp [hxy] at h
    linarith

-- Helper lemma: Quadratic formula solution for y-coordinates
  have h10 : ∀ y : ℝ, y ^ 2 + y - 29 = 0 → y = (-1 + √117) / 2 ∨ y = (-1 - √117) / 2:= by
    intro y hy
    replace hy : (y - (-1 + √117) / 2) * (y - (-1 - √117) / 2) = 0:= by
      ring_nf
      field_simp
      linarith
    simp at hy
    rcases hy with hy | hy
    .
      left
      linarith
    .
      right
      linarith

-- Apply quadratic formula to each y-coordinate
  replace h5:= h10 y1 h5
  replace h6:= h10 y2 h6
  replace h7:= h10 y3 h7
  replace h8:= h10 y4 h8

-- This section handles all possible combinations of y-values using case analysis
-- Each y-value can be either (-1 + √117)/2 or (-1 - √117)/2
  rcases h5 with h5 | h5
  .
    -- Case 1: First y-value is (-1 + √117)/2
    rcases h6 with h6 | h6
    .
      -- Case 1.1: Second y-value is (-1 + √117)/2
      rcases h7 with h7 | h7
      .
        -- Case 1.1.1: Third y-value is (-1 + √117)/2
        -- This case is impossible as it would make x1 = x2 = 0, contradicting h
        by_contra _
        have t1:= h9 x1 x2 g1 (by linarith)
        have t2:= h9 x1 x3 g2 (by linarith)
        have t3:= h9 x2 x3 g4 (by linarith)
        replace t1 : x1 = 0:= by linarith
        replace t2 : x2 = 0:= by linarith
        rw [←t2] at t1
        trivial
      .
        -- Case 1.1.2: Third y-value is (-1 - √117)/2
        rcases h8 with h8 | h8
        .
          -- Case 1.1.2.1: Fourth y-value is (-1 + √117)/2
          -- This case is impossible for similar reasons
          by_contra _
          have t1:= h9 x1 x4 g3 (by linarith)
          have t2:= h9 x1 x2 g1 (by linarith)
          have t3:= h9 x2 x4 g5 (by linarith)
          replace t1 : x1 = 0:= by linarith
          replace t2 : x2 = 0:= by linarith
          rw [←t2] at t1
          trivial
        .
          -- Case 1.1.2.2: Fourth y-value is (-1 - √117)/2
          -- This is a valid case, solve using linarith
          rw [h5, h6, h7, h8]
          linarith
    .
      rcases h7 with h7 | h7
      .
        rcases h8 with h8 | h8
        .
          by_contra _
          have t1:= h9 x1 x4 g3 (by linarith)
          have t2:= h9 x1 x3 g2 (by linarith)
          have t3:= h9 x3 x4 g6 (by linarith)
          replace t1 : x1 = 0:= by linarith
          replace t2 : x3 = 0:= by linarith
          rw [←t2] at t1
          trivial
        .
          rw [h5, h6, h7, h8]
          linarith
      .
        rcases h8 with h8 | h8
        .
          rw [h5, h6, h7, h8]
          linarith
        .
          by_contra _
          have t1:= h9 x2 x3 g4 (by linarith)
          have t2:= h9 x2 x4 g5 (by linarith)
          have t3:= h9 x3 x4 g6 (by linarith)
          replace t1 : x2 = 0:= by linarith
          replace t2 : x3 = 0:= by linarith
          rw [←t2] at t1
          trivial
  .
    rcases h6 with h6 | h6
    .
      rcases h7 with h7 | h7
      .
        rcases h8 with h8 | h8
        .
          by_contra _
          have t1:= h9 x2 x3 g4 (by linarith)
          have t2:= h9 x2 x4 g5 (by linarith)
          have t3:= h9 x3 x4 g6 (by linarith)
          replace t1 : x2 = 0:= by linarith
          replace t2 : x3 = 0:= by linarith
          rw [←t2] at t1
          trivial
        .
          rw [h5, h6, h7, h8]
          linarith
      .
        rcases h8 with h8 | h8
        .
          rw [h5, h6, h7, h8]
          linarith
        .
          by_contra _
          have t1:= h9 x1 x3 g2 (by linarith)
          have t2:= h9 x1 x4 g3 (by linarith)
          have t3:= h9 x3 x4 g6 (by linarith)
          replace t1 : x1 = 0:= by linarith
          replace t2 : x3 = 0:= by linarith
          rw [←t2] at t1
          trivial
    .
      rcases h7 with h7 | h7
      .
        rcases h8 with h8 | h8
        .
          rw [h5, h6, h7, h8]
          linarith
        .
          by_contra _
          have t1:= h9 x1 x4 g3 (by linarith)
          have t2:= h9 x1 x2 g1 (by linarith)
          have t3:= h9 x2 x4 g5 (by linarith)
          replace t1 : x1 = 0:= by linarith
          replace t2 : x2 = 0:= by linarith
          rw [←t2] at t1
          trivial
      .
        by_contra _
        have t1:= h9 x1 x2 g1 (by linarith)
        have t2:= h9 x1 x3 g2 (by linarith)
        have t3:= h9 x2 x3 g4 (by linarith)
        replace t1 : x1 = 0:= by linarith
        replace t2 : x2 = 0:= by linarith
        rw [←t2] at t1
        trivial
