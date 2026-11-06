import Mathlib

open Real

theorem algebra_300688 {x : ℝ} (hx : x^2 - ⌊x⌋ = 2) :
    x ∈ Set.Ioo (-2) 2 ↔ x = -1 ∨ x = sqrt 3 := by
  constructor
  · -- Assume x ∈ (-2, 2)
    intro h
    rcases h with ⟨h1, h2⟩

    have h3 : ⌊x⌋ ≤ (x : ℝ) := by
      exact Int.floor_le x

    have h4 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x

    have h5 : ⌊x⌋ ≤ 1 := by
      by_contra h6
      push_neg at h6

      have h6' : ⌊x⌋ ≥ 2 := by omega
      have h7 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
        exact_mod_cast h6'

      have h8 : (x : ℝ) ≥ (2 : ℝ) := by
        linarith [h7, h3]

      linarith

    have h6 : ⌊x⌋ ≥ -2 := by
      by_contra h7
      push_neg at h7

      have h7' : ⌊x⌋ ≤ -3 := by omega
      have h8 : (⌊x⌋ : ℝ) ≤ (-3 : ℝ) := by
        exact_mod_cast h7'

      have h9 : (x : ℝ) < (-2 : ℝ) := by
        nlinarith [h4, h8]

      linarith

    have h7 : ⌊x⌋ ≤ 1 := by linarith
    have h8 : ⌊x⌋ ≥ -2 := by linarith
    have h10 : ⌊x⌋ = -2 ∨ ⌊x⌋ = -1 ∨ ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 := by omega
    rcases h10 with (h10 | h10 | h10 | h10)
    · -- Case ⌊x⌋ = -2
      have h8 : (⌊x⌋ : ℝ) = -2 := by exact_mod_cast h10

      have eq1 : x^2 = 0 := by
        have eq2 : (⌊x⌋ : ℝ) = -2 := by exact_mod_cast h10
        nlinarith [hx, eq2]

      have eq2 : x = 0 := by
        nlinarith

      have h9 : x < (-1 : ℝ) := by
        have h10' : ⌊x⌋ = -2 := by omega
        have h10'1 : (⌊x⌋ : ℝ) = -2 := by exact_mod_cast h10'
        nlinarith [Int.floor_le x, h10'1]

      nlinarith
    · -- Case ⌊x⌋ = -1
      have h8 : (⌊x⌋ : ℝ) = -1 := by exact_mod_cast h10

      have eq1 : x^2 = 1 := by
        nlinarith [hx, h8]
      have eq2 : x = 1 ∨ x = -1 := by
        have h15 : x^2 = 1 := eq1
        have h16 : (x - 1) * (x + 1) = 0 := by
          nlinarith [h15]
        cases (mul_eq_zero.mp h16) with
        | inl h17 => 
          left
          linarith
        | inr h18 => 
          right
          linarith

      rcases eq2 with (eq2 | eq2)
      · -- x = 1 is invalid for n = -1
        exfalso
        have h14 : x = 1 := eq2
        have h15 : ⌊x⌋ = 1 := by
          rw [h14]
          norm_num
        omega
      · -- x = -1 is valid
        left
        linarith
    · -- Case ⌊x⌋ = 0
      have h8 : (⌊x⌋ : ℝ) = 0 := by exact_mod_cast h10

      have eq1 : x^2 = 2 := by
        nlinarith [hx, h8]
      have h9 : 0 ≤ x := by
        have h10' : ⌊x⌋ = 0 := by omega
        have h10'1 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h10'
        nlinarith [Int.floor_le x, h10'1]

      have h10 : x < (1 : ℝ) := by
        have h10' : ⌊x⌋ = 0 := by omega
        have h10'1 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h10'
        nlinarith [Int.floor_le x, h10'1, Int.lt_floor_add_one x]

      have eq2 : x = Real.sqrt (2 : ℝ) ∨ x = - Real.sqrt (2 : ℝ) := by
        have eq3 : x^2 = 2 := eq1
        have eq4 : (x) ^ 2 - (2 : ℝ) = 0 := by linarith
        have eq5 : (x - Real.sqrt (2 : ℝ)) * (x + Real.sqrt (2 : ℝ)) = 0 := by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
        cases (mul_eq_zero.mp eq5) with
        | inl h => 
          left
          linarith
        | inr h => 
          right
          linarith

      rcases eq2 with (eq2 | eq2)
      · -- x = sqrt 2 is invalid for n = 0
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
      · -- x = -sqrt 2 is invalid for n = 0
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith)]
    · -- Case ⌊x⌋ = 1
      have h8 : (⌊x⌋ : ℝ) = 1 := by exact_mod_cast h10

      have eq1 : x^2 = 3 := by
        nlinarith [hx, h8]
      have h9 : 1 ≤ x := by
        have h10' : ⌊x⌋ = 1 := by omega
        have h10'1 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h10'
        nlinarith [Int.floor_le x, h10'1]

      have h10 : x < (2 : ℝ) := by
        have h10' : ⌊x⌋ = 1 := by omega
        have h10'1 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h10'
        nlinarith [Int.floor_le x, h10'1, Int.lt_floor_add_one x]

      have eq2 : x = Real.sqrt (3 : ℝ) ∨ x = - Real.sqrt (3 : ℝ) := by
        have eq3 : x^2 = 3 := eq1
        have eq4 : (x) ^ 2 - (3 : ℝ) = 0 := by linarith
        have eq5 : (x - Real.sqrt (3 : ℝ)) * (x + Real.sqrt (3 : ℝ)) = 0 := by nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
        cases (mul_eq_zero.mp eq5) with
        | inl h => 
          left
          linarith
        | inr h => 
          right
          linarith

      rcases eq2 with (eq2 | eq2)
      · -- x = sqrt 3 is valid
        right
        linarith
      · -- x = -sqrt 3 is invalid
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
  · -- Assume x = -1 ∨ x = sqrt 3
    intro h
    rcases h with (h | h)
    · -- Case x = -1
      rw [h]
      constructor 
      · -- Show -1 is in (-2, 2)
        norm_num
      · -- Show (-1)^2 - ⌊-1⌋ = 2 
        norm_num
    · -- Case x = sqrt 3
      rw [h]
      have h1 : (Real.sqrt (3 : ℝ) : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)
      have h2 : Real.sqrt (3 : ℝ) > (0 : ℝ) := by
        apply Real.sqrt_pos.mpr 
        norm_num
      constructor
      · -- Show -2 < Real.sqrt (3 : ℝ)
        have h11 : Real.sqrt (3 : ℝ) > (0 : ℝ) := by
          apply Real.sqrt_pos.mpr 
          norm_num
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
      · -- Show Real.sqrt (3 : ℝ) < (2 : ℝ)
        have h12 : Real.sqrt (3 : ℝ) < (2 : ℝ) := by 
          rw [Real.sqrt_lt] <;> norm_num
        linarith