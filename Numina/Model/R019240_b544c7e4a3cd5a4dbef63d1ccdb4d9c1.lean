import Mathlib

theorem number_theory_893
(a : ℚ) : ⌊a⌋ + ⌊-a⌋ = 0 ∨ ⌊a⌋ + ⌊-a⌋ = -1 := by
  have h4 : ⌊a⌋ ≤ a := by
    exact Int.floor_le a
  have h5 : a < ⌊a⌋ + 1 := by
    exact Int.lt_floor_add_one a
  have h6 : ⌊-a⌋ ≤ -a := by
    exact Int.floor_le (-a)
  have h7 : -a < ⌊-a⌋ + 1 := by
    exact Int.lt_floor_add_one (-a)
  have h8 : (⌊a⌋ : ℚ) ≤ a := by exact_mod_cast h4
  have h9 : a < (⌊a⌋ + 1 : ℚ) := by exact_mod_cast h5
  have h10 : (⌊-a⌋ : ℚ) ≤ -a := by exact_mod_cast h6
  have h11 : -a < (⌊-a⌋ + 1 : ℚ) := by exact_mod_cast h7
  have h12 : (⌊a⌋ + ⌊-a⌋ : ℚ) ≤ (0 : ℚ) := by
    linarith
  have h13 : (⌊a⌋ + ⌊-a⌋ : ℚ) + 2 > (0 : ℚ) := by
    linarith
  have h14 : ⌊a⌋ + ⌊-a⌋ ≤ 0 := by
    exact_mod_cast h12
  have h15 : ⌊a⌋ + ⌊-a⌋ + 2 > 0 := by
    exact_mod_cast h13
  omega