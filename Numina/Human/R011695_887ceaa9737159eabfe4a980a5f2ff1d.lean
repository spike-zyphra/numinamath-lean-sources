import Mathlib

/- $30 \cdot 28$ If $x$ is a natural number, let $y=x^{4}+2 x^{3}+2 x^{2}+2 x+1$, then
(A) $y$ must be a perfect square.
(B) There are a finite number of $x$ such that $y$ is a perfect square.
(C) $y$ must not be a perfect square.
(D) There are infinitely many $x$ such that $y$ is a perfect square.
(China Partial Provinces and Cities Junior High School Mathematics Correspondence Competition, 1990) -/
theorem algebra_144975 (y : ℕ → ℕ) (hy : ∀ x, y x = x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 + 2 * x + 1) :
    ¬ (∀ x, IsSquare (y x)) := by
    --Push negation and get the equivalent goal ∃ x, ¬IsSquare (y x)
    push_neg
    --Clearly 1 is a witness
    use 1
    --Use the defintion of y at 1
    specialize hy 1
    simp at hy
    rw [hy]
    rw [IsSquare]
    -- Push the negation through the existential
    push_neg
    -- Introduce k and assume k^2 = 8
    intro k
    -- Show that no natural k satisfies k^2 = 8
    have h : k ^ 2 ≠ 8 := by
      -- Cases on k (since we're dealing with naturals)
      cases k with
      | zero => simp  -- 0^2 = 0 ≠ 8
      | succ k =>
        -- For k ≥ 1, check possible values
        cases k with
        | zero => simp  -- 1^2 = 1 ≠ 8
        | succ k =>
          cases k with
          | zero => simp  -- 2^2 = 4 ≠ 8
          | succ k =>
            -- For k ≥ 3, k^2 ≥ 9 > 8
            have h_lb : (k + 3) ^ 2 ≥ 9 := by
              have : (k + 3)^2 = k^2 + 6 * k + 9 := by ring
              rw [this]
              omega
            linarith
    -- Finish the proof
    rw [pow_two] at h
    exact id (Ne.symm h)