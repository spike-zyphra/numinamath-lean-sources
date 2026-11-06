import Mathlib

theorem algebra_619696 :
    {p : ℝ | ∃! x, x ^ 2 - p * x + p = 0}.ncard = 2 := by
  have h1 : {p : ℝ | ∃! x, x ^ 2 - p * x + p = 0} = {0, 4} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward: if $p \in \{p : ℝ | ∃! x, x ^ 2 - p * x + p = 0\}$, then $p \in \{0, 4\}$
      intro h
      rcases h with ⟨x, ⟨hx1, hx2⟩⟩
      -- Define $y = p - x$, then $y$ is also a solution
      have h_eq1 : (p - x) ^ 2 - p * (p - x) + p = 0 := by 
        nlinarith [hx1]
      -- Use uniqueness to get $y = x$, so $p - x = x \implies p = 2x$
      have h_eq3 : p - x = x := by 
        apply hx2 
        exact h_eq1 
      have h_eq4 : p = 2 * x := by 
        linarith 
      -- Substitute $p = 2x$ into $x^2 - px + p = 0$
      rw [h_eq4] at hx1 
      -- Simplify to get $x^2 - 2x^2 + 2x = 0 \implies -x^2 + 2x = 0 \implies x(-x + 2) = 0$
      have heq4 : x * (-x + 2) = 0 := by 
        nlinarith [hx1]
      have h2 : p = 0 ∨ p = 4 := by
        have hx0 : x = 0 ∨ x = 2 := by 
          cases (mul_eq_zero.mp heq4) with
          | inl h1 => 
            left 
            linarith 
          | inr h2 => 
            right
            linarith 
        cases hx0 with
        | inl hx1 => 
          left
          rw [hx1] at h_eq4
          linarith 
        | inr hx1 => 
          right 
          rw [hx1] at h_eq4 
          linarith 
      tauto 
    · -- Reverse: if $p \in \{0, 4\}$, then $p \in \{p : ℝ | ∃! x, x ^ 2 - p * x + p = 0\}$
      rintro (rfl | rfl)
      · -- When $p = 0$: The equation becomes $x^2 = 0$
        use (0 : ℝ)
        constructor
        · -- Show $0$ is a solution
          norm_num
        · -- Show it is the unique solution
          intro y hy
          have hy' : y ^ 2 = 0 := by
            nlinarith 
          have : y = 0 := by 
            nlinarith 
          tauto 
      · -- When $p = 4$: The equation becomes $x^2 -4x + 4 = 0$
        use (2 : ℝ)
        constructor
        · -- Show $2$ is a solution
          norm_num
        · -- Show it is the unique solution
          intro y hy
          have : (y - 2) ^ 2 = 0 := by
            nlinarith 
          have : y = 2 := by
            nlinarith 
          tauto 
  rw [h1] 
  rw [Set.ncard_pair (by norm_num)]