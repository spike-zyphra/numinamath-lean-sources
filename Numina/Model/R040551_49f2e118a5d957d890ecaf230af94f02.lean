import Mathlib

open Set Real Int Nat

theorem algebra_104795 {n : ℕ} :
    {x : ℝ | x^2 + ⌊x⌋ ≤ n} ⊆ {x : ℝ | ⌊x^2⌋ + x ≤ n + 1} ∧
    {x : ℝ | ⌊x^2⌋ + x ≤ n} ⊆ {x : ℝ | x^2 + ⌊x⌋ ≤ n + 1} := by
  constructor
  · -- First, prove that $A_n \subseteq B_{n+1}$.
    intro x h
    have h1 : x ^ 2 + (⌊x⌋ : ℝ) ≤ (n : ℝ) := by
      simpa using h
    have h2 : (⌊x^2⌋ : ℝ) + x ≤ (n + 1 : ℝ) := by
      have hx1 : ⌊x⌋ ≤ (x) := Int.floor_le x
      have hx2 : (x) < ⌊x⌋ + 1 := Int.lt_floor_add_one x
      have hx4 : (⌊x^2⌋ : ℝ) ≤ x^2 := by
        exact Int.floor_le (x ^ 2)
      have h2' : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast Int.lt_floor_add_one x
      have h1' : x ^ 2 + (⌊x⌋ : ℝ) ≤ (n : ℝ) := h1
      norm_num at *
      nlinarith [sq_nonneg ((x - ⌊x⌋ : ℝ) ), sq_nonneg (x + ⌊x⌋ : ℝ), 
        Int.floor_le (x ^ 2), Int.floor_le (x), 
        Int.lt_floor_add_one (x ^ 2),
        Int.lt_floor_add_one x, 
        sq_nonneg ((x^2 - (⌊x^2⌋ : ℝ)) : ℝ)
      ]
    simpa using h2
  · -- Now, prove $B_n \subseteq A_{n+1}$.
    intro x h
    have h1 : (⌊x^2⌋ : ℝ) + x ≤ (n : ℝ) := by
      simpa using h
    have h2 : x^2 + (⌊x⌋ : ℝ) ≤ (n + 1 : ℝ) := by
      have hx1 : ⌊x⌋ ≤ (x) := Int.floor_le x
      have hx2 : (x) < ⌊x⌋ + 1 := Int.lt_floor_add_one x
      have hx4 : (⌊x^2⌋ : ℝ) ≤ x^2 := by
        exact Int.floor_le (x ^ 2)
      have h2' : x < (⌊x⌋ + 1 : ℝ) := by
        exact_mod_cast Int.lt_floor_add_one x
      -- a bound from x to floor(x^2)
      norm_num at *
      nlinarith [sq_nonneg ((x - ⌊x⌋ : ℝ) ), sq_nonneg (x + ⌊x⌋ : ℝ), 
        Int.floor_le (x ^ 2), Int.floor_le (x), 
        Int.lt_floor_add_one (x ^ 2),
        Int.lt_floor_add_one x, 
        sq_nonneg ((x^2 - (⌊x^2⌋ : ℝ)) : ℝ)
      ]
    simpa using h2