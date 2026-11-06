import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_7864 :
  (sSup {t : ℝ | ∃ x y, t = 4 * x + 3 * y ∧ 3 * x + 5 * y ≤ 10 ∧ y ≤ x + 2 ∧ y ≥ -1} +
   sInf {t : ℝ | ∃ x y, t = 4 * x + 3 * y ∧ 3 * x + 5 * y ≤ 10 ∧ y ≤ x + 2 ∧ y ≥ -1}) / 2 = 1 := by
  have h1 : sSup {t : ℝ | ∃ x y, t = 4 * x + 3 * y ∧ 3 * x + 5 * y ≤ 10 ∧ y ≤ x + 2 ∧ y ≥ -1} = 17 := by
    have h2 : {t : ℝ | ∃ x y, t = 4 * x + 3 * y ∧ 3 * x + 5 * y ≤ 10 ∧ y ≤ x + 2 ∧ y ≥ -1} = Set.Icc (-15 : ℝ) (17 : ℝ) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · -- Assume $t \in \{t : \mathbb{R} | \exists x y, t = 4x + 3y \wedge 3x + 5y \leq 10 \wedge y \leq x + 2 \wedge y \geq -1\}$, prove $t \in \{-15, 17\}$.
        rintro ⟨x, y, h_eq, h1, h2, h3⟩
        constructor
        · -- Show that -15 ≤ t
          linarith
        · -- Show that t ≤ 17
          linarith
      · -- Assume $t \in \{-15, 17\}$, prove $t \in \{t : \mathbb{R} | \exists x y, t = 4x + 3y \wedge 3x + 5y \leq 10 \wedge y \leq x + 2 \wedge y \geq -1\}$.
        rintro ⟨ht1, ht2⟩
        use (t + 3) / 4, -1
        constructor
        · -- Show $t = 4x + 3y$
          linarith
        constructor
        · -- Show $3x + 5y \leq 10$
          linarith
        constructor
        · -- Show $y \leq x + 2$
          linarith
        · -- Show $y \geq -1$
          linarith
    rw [h2]
    norm_num
  have h3 : sInf {t : ℝ | ∃ x y, t = 4 * x + 3 * y ∧ 3 * x + 5 * y ≤ 10 ∧ y ≤ x + 2 ∧ y ≥ -1} = -15 := by
    have h2 : {t : ℝ | ∃ x y, t = 4 * x + 3 * y ∧ 3 * x + 5 * y ≤ 10 ∧ y ≤ x + 2 ∧ y ≥ -1} = Set.Icc (-15 : ℝ) (17 : ℝ) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · -- Assume $t \in \{t : \mathbb{R} | \exists x y, t = 4x + 3y \wedge 3x + 5y \leq 10 \wedge y \leq x + 2 \wedge y \geq -1\}$, prove $t \in \{-15, 17\}$.
        rintro ⟨x, y, h_eq, h1, h2, h3⟩
        constructor
        · -- Show that -15 ≤ t
          linarith
        · -- Show that t ≤ 17
          linarith
      · -- Assume $t \in \{-15, 17\}$, prove $t \in \{t : \mathbb{R} | \exists x y, t = 4x + 3y \wedge 3x + 5y \leq 10 \wedge y \leq x + 2 \wedge y \geq -1\}$.
        rintro ⟨ht1, ht2⟩
        use (t + 3) / 4, -1
        constructor
        · -- Show $t = 4x + 3y$
          linarith
        constructor
        · -- Show $3x + 5y \leq 10
  -- Show the constraint 3x + 5y ≤ 10 is satisfied
          linarith
        constructor
        · -- Show $y \leq x + 2
  -- Show the constraint y ≤ x + 2 is satisfied
          linarith
        · -- Show $y \geq -1
  -- Show the constraint y ≥ -1 is satisfied
          linarith
    rw [h2]
    norm_num
  rw [h1, h3]
  all_goals norm_num