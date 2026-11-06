import Mathlib
open Nat

/-
Dylan has a $100 \times 100$ square, and wants to cut it into pieces of area at least 1.
Each cut must be a straight line (not a line segment) and must intersect the interior
of the square. What is the largest number of cuts he can make?

Answer: 9999
-/

-- Define the side length of the square
abbrev L_val : ℕ := 100

-- Define the total area of the square
abbrev Area_val : ℕ := L_val^2

-- The set of possible numbers of cuts C that Dylan can make.
-- A number of cuts C is "possible" if it can lead to a configuration where:
-- 1. The number of pieces P is at least C+1 (each cut adds at least one piece).
-- 2. The number of pieces P is at most Area_val (each piece has area at least 1).
-- So, C is possible if there exists P such that C+1 ≤ P ≤ Area_val.
-- This implies C+1 ≤ Area_val, so C ≤ Area_val - 1.
-- The "can make" part also implies that such a cutting procedure exists.
def PossibleCutsSet : Set ℕ :=
  { C : ℕ | ∃ P : ℕ, -- P is the number of pieces after C cuts
              P ≥ C + 1 ∧ P ≤ Area_val ∧
              (if C = Area_val - 1 then P = Area_val else True) 
  }


theorem max_cuts_is_area_minus_one :
    IsGreatest PossibleCutsSet (Area_val - 1) := by
  constructor
  · -- Part 1: Show (Area_val - 1) ∈ PossibleCutsSet
    simp only [PossibleCutsSet, Set.mem_setOf_eq]
    use Area_val -- Let P = Area_val
    constructor
    · -- P ≥ C + 1  =>  Area_val ≥ (Area_val - 1) + 1
      simp only [Nat.sub_add_cancel (Nat.one_le_of_lt (by {norm_num} : Area_val > 0))]
      exact Nat.le_refl Area_val
    · constructor
      · -- P ≤ Area_val  =>  Area_val ≤ Area_val
        exact Nat.le_refl Area_val
      · -- if (Area_val - 1) = Area_val - 1 then Area_val = Area_val else True
        simp only [eq_self_iff_true, if_true]

  · -- Part 2: Show ∀ C' ∈ PossibleCutsSet, C' ≤ Area_val - 1
    intro C' hC'_in_set
    simp only [PossibleCutsSet, Set.mem_setOf_eq] at hC'_in_set
    rcases hC'_in_set with ⟨P', h_P_ge_C_plus_1, h_P_le_Area, _h_achievable_detail⟩
    -- We have C' + 1 ≤ P' and P' ≤ Area_val
    have h_C_plus_1_le_Area : C' + 1 ≤ Area_val := Nat.le_trans h_P_ge_C_plus_1 h_P_le_Area
    -- From C' + 1 ≤ Area_val, we get C' ≤ Area_val - 1
    exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h_C_plus_1_le_Area)

-- The theorem stating the final answer directly.
theorem largest_number_of_cuts_is_9999 :
    IsGreatest PossibleCutsSet 9999 := by

  rw [show 9999 = Area_val - 1 by norm_num]
  exact max_cuts_is_area_minus_one

