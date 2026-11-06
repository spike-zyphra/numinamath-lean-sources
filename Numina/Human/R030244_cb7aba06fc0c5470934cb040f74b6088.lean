import Mathlib

/- For what ordered pair $(a,b)$ are there infinite solutions $(x,y)$ to the system \begin{align*}
3ax+3y&=5b,\\
2x+y&=5.
\end{align*} -/
theorem algebra_21293 : { (a, b) : ℝ × ℝ | {(x, y) | 3 * a * x + 3 * y = 5 * b ∧ 2 * x + y = 5}.Infinite } = {(2, 3)} := by
  -- We have two goals:
  -- 1. If the equation system has infinite solutions, then (a, b) = (2, 3)
  -- 2. If (a, b) = (2, 3), then the equation system has infinite solutions
  ext ⟨a, b⟩
  simp
  constructor
  . -- First goal
    intro h
    -- We prove a = 2 by contradiction
    have ha : a = 2 := by
      by_contra! ha
      -- If a ≠ 2, then the equation system has a unique solution
      have k : {(x, y) | 3 * a * x + 3 * y = 5 * b ∧ 2 * x + y = 5} = {((5*b-15)/(3*a-6), (15*a-10*b)/(3*a-6))} := by
        ext ⟨x, y⟩
        simp
        -- Replace ha with 3*a-6 ≠ 0
        replace ha : 3*a-6 ≠ 0 := by
          contrapose! ha
          linarith only [ha]
        constructor
        . intro ⟨h1, h2⟩
          -- We prove x * (3*a-6) = 5*b-15 ∧ y * (3*a-6) = 15*a-10*b
          have ⟨hx, hy⟩ : x * (3*a-6) = 5*b-15 ∧ y * (3*a-6) = 15*a-10*b := by
            constructor
            -- They are linear combinations of h1 and h2
            . linear_combination h1 - 3 * h2
            . linear_combination -(2 * h1) + 3 * a * h2
          -- We prove x = (5*b-15)/(3*a-6) ∧ y = (15*a-10*b)/(3*a-6), which is trivial after field simplification
          constructor
          . field_simp
            exact hx
          . field_simp
            exact hy
        . -- Check x = (5*b-15)/(3*a-6), y = (15*a-10*b)/(3*a-6) is a solution
          rintro ⟨rfl, rfl⟩
          field_simp
          ring_nf
          simp
      -- Singleton set can't be infinite
      rw [k] at h
      simp at h
    -- Substitute a = 2
    subst ha
    simp
    -- We prove b = 3 by contradiction
    by_contra! hb
    -- If b ≠ 3, then the equation system has no solutions
    have k : {(x, y) | 3 * 2 * x + 3 * y = 5 * b ∧ 2 * x + y = 5} = ∅ := by
      ext ⟨x, y⟩
      simp
      intro h1 h2
      -- We get b = 3 from h1 and h2
      absurd hb
      linear_combination -1 * h1 / 5 + 3 / 5 * h2
    -- Empty set can't be infinite
    rw [k] at h
    simp at h
    -- The first goal is done.
  . -- Second goal
    rintro ⟨rfl, rfl⟩
    -- We prove the equation system has infinite solutions
    -- The solution set is {(x, 5-2*x) | x ∈ ℝ}
    have k : {(x, y) : ℝ × ℝ | 3 * 2 * x + 3 * y = 5 * 3 ∧ 2 * x + y = 5} = Set.range (fun x => (x, 5-2*x)) := by
      ext ⟨x, y⟩
      simp
      -- Simple linarith
      constructor
      . rintro ⟨-, h⟩
        linarith
      . intro h
        constructor <;> linarith
    rw [k]
    -- The range of an injective function from infinite domain is infinite
    apply Set.infinite_range_of_injective
    -- Prove x ↦ (x, 5-2*x) is injective
    intro x y h
    simp at h
    exact h
