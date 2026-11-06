import Mathlib
open Real

theorem AIME_NumberTheory_732   :
  IsLeast {(t:ℝ) | (t > 0) ∧ (∃ (x: Nat), 2 * π * t / 60-2 * π * t / 84=x*π )∧(∃ (y: Nat), 2 * π * t / 84-2 * π * t / 140=y*π ) }  105 := by
  constructor
  · -- Show 105 is in the set.
    constructor
    · norm_num
    constructor
    · -- Show ∃ x : Nat, 2π105 / 60 - 2π105 / 84 = xπ
      use 1
      field_simp
      <;> ring
    · -- Show ∃ y : Nat, 2π105 / 84 - 2π105 / 140 = yπ
      use 1
      field_simp
      <;> ring
  · -- Show no other element is smaller.
    intro t ⟨ht1, ⟨x, hx⟩, ⟨y, hy⟩⟩
    have eq1 : 2 * π * t / 60 - 2 * π * t / 84 = x * π := by
      simpa using hx
    have eq2 : 2 * π * t / 84 - 2 * π * t / 140 = y * π := by
      simpa using hy
    have eq3 : 2 * t / 60 - 2 * t / 84 = (x : ℝ) := by
      have h := eq1
      have : π ≠ 0 := Real.pi_ne_zero
      apply (mul_left_inj' this).mp
      linarith
    have eq4 : 2 * t / 84 - 2 * t / 140 = (y : ℝ) := by
      have h := eq2
      have : π ≠ 0 := Real.pi_ne_zero
      apply (mul_left_inj' this).mp
      linarith
    have hx2 : x > 0 := by
      have h1 : (t : ℝ) > (0 : ℝ) := ht1
      have h2 : (t : ℝ) = (105 : ℝ) * (x : ℝ) := by
        norm_num at eq3
        nlinarith
      have h3 : (x : ℝ) > (0 : ℝ) := by
        nlinarith [h1, h2]
      have hx2 : x > 0 := by
        by_contra h
        push_neg at h
        have h0 : x ≤ 0 := by linarith
        have h1 : (x : ℝ) ≤ (0 : ℝ) := by
          exact_mod_cast h0
        linarith
      exact_mod_cast hx2
    have hx22 : x ≥ 1 := by
      nlinarith
    -- Convert the original equations to multiples of π.
    have h4 : t ≥ 105 := by
      norm_num at eq3 eq4
      have eq5 : t = (105 : ℝ) * (x : ℝ) := by
        nlinarith
      have h22 : (x : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast hx22
      nlinarith [eq5, h22]
    linarith