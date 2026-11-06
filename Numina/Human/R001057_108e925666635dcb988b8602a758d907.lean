import Mathlib

/- Two fair 6-sided dice are rolled.  What is the probability the sum rolled is 9? -/
theorem algebra_20231 : (Set.ncard {(x, y) : ℕ × ℕ | x ∈ Finset.Icc 1 6 ∧ y ∈ Finset.Icc 1 6 ∧ x + y = 9}) / (36 : ℝ) = 1 / 9 := by
  -- It suffices to show that there are 4 ways to roll a sum of 9
  suffices _ : Set.ncard {(x, y) : ℕ × ℕ | x ∈ Finset.Icc 1 6 ∧ y ∈ Finset.Icc 1 6 ∧ x + y = 9} = (4 : ℝ) by linarith
  norm_cast

  -- As long as we show that the set of pairs (x, y) such that x + y = 9 is {(3, 6), (4, 5), (5, 4), (6, 3)}, we are done
  suffices H : {(x, y) : ℕ × ℕ | x ∈ Finset.Icc 1 6 ∧ y ∈ Finset.Icc 1 6 ∧ x + y = 9} = {(3, 6), (4, 5), (5, 4), (6, 3)} by
    rw [H,
        show ({(3, 6), (4, 5), (5, 4), (6, 3)} : Set (ℕ × ℕ)) = ({(3, 6), (4, 5), (5, 4), (6, 3)} : Finset (ℕ × ℕ)) by simp, -- Coercion from Set to Finset
        Set.ncard_coe_Finset]
    simp

  -- We show that the set of pairs (x, y) such that x + y = 9 is {(3, 6), (4, 5), (5, 4), (6, 3)}
  -- We prove mutual inclusion
  ext ⟨x, y⟩
  simp
  constructor
  . -- First inclusion
    rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hxy⟩
    -- 1 ≤ x ≤ 6, we just check all the cases
    interval_cases x
    all_goals
      -- Linear arithmetic in ℕ
      omega
  . -- Second inclusion, we check all the cases
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      simp
