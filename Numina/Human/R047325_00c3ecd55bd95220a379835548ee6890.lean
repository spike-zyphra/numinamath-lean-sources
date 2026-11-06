import Mathlib

open Real Set
open scoped BigOperators

/-Point $A$ lies somewhere within or on the square which has opposite corners at $(0,0)$ and $(2,2)$. Point $B$ lies somewhere within or on the square which has opposite corners at points $(4,2)$ and $(5,3)$. What is the greatest possible value of the slope of the line containing points $A$ and $B$? Express your answer as a common fraction.-/
theorem algebra_21211:
    IsGreatest {m | ∃A B: ℝ × ℝ, A ∈ {p | p.1 ∈ Icc 0 2 ∧ p.2 ∈ Icc 0 2} ∧ B ∈ {p | p.1 ∈ Icc 4 5 ∧ p.2 ∈ Icc 2 3} ∧ m = (B.2 - A.2) / (B.1 - A.1)} (3 / (2 : ℝ)) := by
  -- simplify the desired conclusion
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  -- show that 3 / 2 can be equal
  . -- A = (2, 0)
    use 2, 0
    norm_num
    -- B = (4, 3)
    use 4, 3
    norm_num
  -- show that the slope is less than 3 / 2
  . intro m A1 A2 _ hA1₂ hA2₁ _ B1 B2 hB1₁ _ _ hB2₂ hm
    -- show that B2 - A2 ≤ 3
    have ineq₁ : B2 - A2 ≤ 3 := by
      calc
        B2 - A2 ≤ 3 - 0 := by apply sub_le_sub; repeat tauto
        _ = 3 := by norm_num
    -- show that 2 ≤ B1 - A1
    have ineq₂ : 2 ≤ B1 - A1 := by
      calc
        2 = 4 - 2 := by norm_num
        _ ≤ B1 - A1 := by apply sub_le_sub; repeat tauto
    -- calc that m ≤ 3 / 2
    calc
      m = (B2 - A2) / (B1 - A1) := by rw [hm]
      _ ≤ 3 / 2 := by
        apply div_le_div
        all_goals linarith only[ineq₁, ineq₂]

