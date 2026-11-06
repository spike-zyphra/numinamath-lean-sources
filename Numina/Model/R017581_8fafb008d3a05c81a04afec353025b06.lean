import Mathlib

theorem number_theory_119718 (x y : ℝ) :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 ∧
    (⌊x⌋ + ⌊y⌋ = ⌊x + y⌋ ∨ ⌊x⌋ + ⌊y⌋ = ⌊x + y⌋ + 1 ∨
     ⌊x⌋ + ⌊y⌋ + 1 = ⌊x + y⌋) := by
  constructor
  · -- Show that $\lfloor x \rfloor + \lfloor y \rfloor \leq \lfloor x + y \rfloor$
    exact Int.le_floor_add x y
  constructor
  · -- Show that $\lfloor x + y \rfloor \leq \lfloor x \rfloor + \lfloor y \rfloor + 1$
    have h1 : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
      have h2 : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := Int.le_floor_add x y
      have h3 : ⌊x + y⌋ < (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by
        have hx1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
        have hx2 : x < (⌊x⌋ + 1 : ℝ) := Int.lt_floor_add_one x
        have hy1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
        have hy2 : y < (⌊y⌋ + 1 : ℝ) := Int.lt_floor_add_one y
        have hxy : x + y < (⌊x⌋ + 1 : ℝ) + (⌊y⌋ + 1 : ℝ) := by linarith
        have h4 : (⌊x + y⌋ : ℝ) ≤ x + y := Int.floor_le (x + y)
        have h5 : (⌊x + y⌋ : ℝ) < (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by linarith
        exact_mod_cast h5
      have h4 : ⌊x + y⌋ < ⌊x⌋ + ⌊y⌋ + 2 := by exact_mod_cast h3
      omega
    exact_mod_cast h1
  · -- Show that one and only one of the equalities holds
    have h1 : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := Int.le_floor_add x y
    have h2 : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by 
      have h1 : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := Int.le_floor_add x y
      have h3 : ⌊x + y⌋ < (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by
        have hx1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
        have hx2 : x < (⌊x⌋ + 1 : ℝ) := Int.lt_floor_add_one x
        have hy1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
        have hy2 : y < (⌊y⌋ + 1 : ℝ) := Int.lt_floor_add_one y
        have hxy : x + y < (⌊x⌋ + 1 : ℝ) + (⌊y⌋ + 1 : ℝ) := by linarith
        have h4 : (⌊x + y⌋ : ℝ) ≤ x + y := Int.floor_le (x + y)
        have h5 : (⌊x + y⌋ : ℝ) < (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by linarith
        exact_mod_cast h5
      have h4 : ⌊x + y⌋ < ⌊x⌋ + ⌊y⌋ + 2 := by exact_mod_cast h3
      omega
    have h3 : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ ∨ ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 := by 
      omega
    rcases h3 with h3 | h3
    · -- Case where $\lfloor x + y \rfloor = \lfloor x \rfloor + \lfloor y \rfloor$
      left
      omega
    · -- Case where $\lfloor x + y \rfloor = \lfloor x \rfloor + \lfloor y \rfloor + 1$
      right
      right
      omega