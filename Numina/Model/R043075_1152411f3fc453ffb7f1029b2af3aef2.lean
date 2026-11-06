import Mathlib

theorem algebra_268610 :
    {(x, y, z) : (ℝ × ℝ × ℝ) | ⌊x⌋ - y = 2004 / 2005 ∧ 2 * ⌊y⌋ - z = 2004 / 2005 ∧ 3 * ⌊z⌋ - x = 2004 / 2005} = {(2 + 1 / 2005, 1 + 1 / 2005, 1 + 1 / 2005)}:= by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First prove that (x, y, z) in the set implies (2 + 1/2005, 1 + 1/2005, 1 + 1/2005).
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : ⌊y⌋ = ⌊x⌋ - 1 := by
      have h5 : ⌊x⌋ ≤ x := by
        exact Int.floor_le x
      have h6 : x < ⌊x⌋ + 1 := by
        exact Int.lt_floor_add_one x
      have eq1 : y = (⌊x⌋ : ℝ) - 2004 / 2005 := by linarith
      have h8 : (⌊x⌋ : ℝ) - 1 < y := by
        nlinarith
      have h9 : y < (⌊x⌋ : ℝ) := by
        nlinarith
      have h10 : ⌊y⌋ = ⌊x⌋ - 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> try nlinarith
      exact h10
    have h12 : ⌊z⌋ = 2 * ⌊x⌋ - 3 := by
      have eq1 : z = 2 * (⌊x⌋ : ℝ) - 2 - 2004 / 2005 := by
        have h13 : (⌊y⌋ : ℝ) = (⌊x⌋ : ℝ) - 1 := by
          exact_mod_cast h4
        nlinarith
      have h13 : ⌊z⌋ = 2 * ⌊x⌋ - 3 := by
        have eq2 : z = (2 * ⌊x⌋ - 3 : ℝ) + (1 / 2005 : ℝ) := by
          nlinarith [eq1]
        have h15 : (2 * ⌊x⌋ - 3 : ℝ) < z := by
          linarith [eq2]
        have h16 : z < (2 * ⌊x⌋ - 3 + 1 : ℝ) := by
          nlinarith [eq2]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try nlinarith)
      exact h13
    have h17 : x = 6 * (⌊x⌋ : ℝ) - 20049 / 2005 := by
      have h18 : (3 * ⌊z⌋ : ℝ) - x = 2004 / 2005 := by
        exact_mod_cast h₃
      have h19 : (⌊z⌋ : ℝ) = (2 * ⌊x⌋ - 3 : ℝ) := by
        exact_mod_cast h12
      nlinarith
    have h18 : ⌊x⌋ = 2 := by
      have eq1 : x = 6 * (⌊x⌋ : ℝ) - 20049 / 2005 := h17
      have h20 : ⌊x⌋ ≤ (6 * (⌊x⌋ : ℝ) - 20049 / 2005 : ℝ) := by
        have h22 : ⌊x⌋ ≤ x := by
          exact Int.floor_le x
        nlinarith
      have h23 : (6 * (⌊x⌋ : ℝ) - 20049 / 2005 : ℝ) < (⌊x⌋ + 1 : ℝ) := by
        have h21 : x < ⌊x⌋ + 1 := by
          exact Int.lt_floor_add_one x
        nlinarith
      have h24 : ⌊x⌋ ≥ 2 := by
        by_contra h
        push_neg at h
        have h26 : ⌊x⌋ ≤ 1 := by omega
        have h27 : (⌊x⌋ : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h26
        nlinarith
      have h25 : ⌊x⌋ ≤ 2 := by
        by_contra h
        push_neg at h
        have h28 : ⌊x⌋ ≥ 3 := by omega
        have h29 : (⌊x⌋ : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h28
        nlinarith
      omega
    have hx : x = 2 + 1 / 2005 := by
      have h19 : (⌊x⌋ : ℝ) = (2 : ℝ) := by
        exact_mod_cast h18
      nlinarith [h17]
    have hy : y = 1 + 1 / 2005 := by
      have eq1 : y = (⌊x⌋ : ℝ) - 2004 / 2005 := by linarith
      have h19 : (⌊x⌋ : ℝ) = (2 : ℝ) := by
        exact_mod_cast h18
      rw [h19] at eq1
      nlinarith
    have hz : z = 1 + 1 / 2005 := by
      have eq1 : z = 2 * (⌊x⌋ : ℝ) - 2 - 2004 / 2005 := by
        have h13 : (⌊y⌋ : ℝ) = (⌊x⌋ : ℝ) - 1 := by
          exact_mod_cast h4
        nlinarith [h₁, h₂, h13]
      have h19 : (⌊x⌋ : ℝ) = (2 : ℝ) := by
        exact_mod_cast h18
      rw [h19] at eq1
      nlinarith
    simp [hx, hy, hz]
  · -- Now prove the reverse.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- First equation.
      norm_num
    constructor
    · -- Second equation.
      norm_num
    · -- Third equation.
      norm_num