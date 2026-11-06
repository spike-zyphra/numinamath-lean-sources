import Mathlib

open Real Set
open scoped BigOperators

/- 2. Let $x, y$ be positive numbers, and $S$ be the smallest number among $x, y+\frac{1}{x}, \frac{1}{y}$.
Find the maximum possible value of $S$. For what values of $x, y$ is this maximum value achieved?
-/

theorem algebra_221829:
    IsGreatest {s : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ s = min (min x (y + 1/x)) (1/y)} (Real.sqrt 2) := by

    constructor
    -- the forward direction
    .
      simp [Set.mem_setOf_eq]
      use √2
      constructor
      .
        apply Real.sqrt_pos_of_pos
        norm_num
      .
        use √2 / 2
        constructor
        .
          have o: 0 < √2 := by apply Real.sqrt_pos_of_pos; norm_num
          linarith
        .
          simp
          have o: (√2)⁻¹ = √2 / 2 := by
            field_simp
          rw [o]
          linarith

    -- the backward direction
    .
      intro s h
      simp only [Set.mem_setOf_eq] at h
      obtain ⟨x, y, hx, hy, h⟩ := h
      have h1: s ≤ x := by
        rw [h]
        simp
      have h2: s ≤ y + 1 / x := by
        rw [h]
        simp
      have h3: s ≤ 1 / y := by
        rw [h]
        simp
      clear h
      by_cases ls: s ≤ 0
      .
        have o: 0 ≤ √2 := by
          apply Real.sqrt_nonneg
        linarith
      .
        replace ls: 0 < s := by
          linarith
        replace h3: y ≤ 1 / s := by
          rw [le_one_div] at h3
          exact h3
          exact ls
          exact hy
        replace h1: 1 / x ≤ 1 / s := by
          apply one_div_le_one_div_of_le
          exact ls
          exact h1
        have l: s ≤ 2 / s := by
          calc
            s ≤ y + 1 / x := h2
            _ ≤ y + 1 / s := by linarith
            _ ≤ 1 / s + 1 / s := by linarith
            _ = 2 / s := by ring
        replace l: s ^ 2 ≤ 2 := by
          rw [le_div_iff₀] at l
          nlinarith
          exact ls
        rw [show 2 = (√2) ^ 2 by norm_num] at l
        rw [sq_le_sq₀] at l
        exact l
        linarith
        norm_num