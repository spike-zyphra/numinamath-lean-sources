import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311839 :
  IsLeast {n | ∃ x y : Fin 3 → ℝ,
    (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧
    n = sqrt ((2018 - y 0 - y 1 - y 2)^2 + x 2^2) +
      sqrt (y 2^2 + x 1^2) +
      sqrt (y 1^2 + x 0^2) +
      sqrt (y 0^2 + (x 0 + x 1 + x 2)^2)} 2018 := by

  constructor
  · -- Show that 2018 is in the set.
    use (fun _ => (0 : ℝ)), (fun _ => (0 : ℝ))
    constructor
    · intro i
      simp
    constructor
    · intro i
      simp
    · -- Show 2018 = ...
      have h1 : sqrt ((2018 - (0 : ℝ) - (0 : ℝ) - (0 : ℝ)) ^ 2 + (0 : ℝ) ^ 2) = (2018 : ℝ) := by
        rw [show (2018 - (0 : ℝ) - (0 : ℝ) - (0 : ℝ)) ^ 2 + (0 : ℝ) ^ 2 = (2018 : ℝ) ^ 2 by ring]
        rw [Real.sqrt_sq]
        all_goals norm_num
      have h2 : sqrt ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = (0 : ℝ) := by
        simp
      simp [h1, h2]
      all_goals norm_num
  · -- Show that 2018 is the minimum
    intro n hn
    rcases hn with ⟨x, y, hx, hy, hn⟩
    have h1 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2) ≥ abs (2018 - y 0 - y 1 - y 2) := by
      have h7 : abs (2018 - y 0 - y 1 - y 2) = sqrt ((2018 - y 0 - y 1 - y 2 : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      have h10 : sqrt ((2018 - y 0 - y 1 - y 2 : ℝ) ^ 2) ≤ sqrt ((2018 - y 0 - y 1 - y 2 : ℝ) ^ 2 + x 2 ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [show 0 ≤ x 2 by specialize hx 2; linarith]
      linarith [h7, h10]
    have h3 : sqrt (y 2 ^ 2 + x 1 ^ 2) ≥ y 2 := by
      have h4 : y 2 ≥ 0 := by specialize hy 2; linarith
      have h5 : sqrt (y 2 ^ 2 + x 1 ^ 2) ≥ sqrt (y 2 ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [show 0 ≤ x 1 by specialize hx 1; linarith]
      have h6 : sqrt (y 2 ^ 2) = y 2 := by
        rw [Real.sqrt_sq (by linarith)]
      nlinarith [h6]
    have h4 : sqrt (y 1 ^ 2 + x 0 ^ 2) ≥ y 1 := by
      have h4 : y 1 ≥ 0 := by specialize hy 1; linarith
      have h5 : sqrt (y 1 ^ 2 + x 0 ^ 2) ≥ sqrt (y 1 ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [show 0 ≤ x 0 by specialize hx 0; linarith]
      have h6 : sqrt (y 1 ^ 2) = y 1 := by
        rw [Real.sqrt_sq (by linarith)]
      nlinarith [h6]
    have h5 : sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ y 0 := by
      have h4 : y 0 ≥ 0 := by specialize hy 0; linarith
      have h5 : sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ sqrt (y 0 ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [show 0 ≤ x 0 + x 1 + x 2 by
          have h1 : x 0 ≥ 0 := by apply hx 0
          have h2 : x 1 ≥ 0 := by apply hx 1
          have h3 : x 2 ≥ 0 := by apply hx 2
          linarith
        ]
      have h6 : sqrt (y 0 ^ 2) = y 0 := by
        rw [Real.sqrt_sq (by linarith)]
      nlinarith [h6]
    have h6 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2) +
        sqrt (y 2 ^ 2 + x 1 ^ 2) + sqrt (y 1 ^ 2 + x 0 ^ 2) + sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ 2018 := by
      have h7 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2) + sqrt (y 2 ^ 2 + x 1 ^ 2) + sqrt (y 1 ^ 2 + x 0 ^ 2) + sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ abs (2018 - y 0 - y 1 - y 2) + y 2 + y 1 + y 0 := by
        linarith [h1, h3, h4, h5]
      have h8 : abs (2018 - y 0 - y 1 - y 2) + y 2 + y 1 + y 0 ≥ 2018 := by
        cases' abs_cases (2018 - y 0 - y 1 - y 2) with h h <;> linarith
      linarith [h7, h8]
    linarith [hn, h6]