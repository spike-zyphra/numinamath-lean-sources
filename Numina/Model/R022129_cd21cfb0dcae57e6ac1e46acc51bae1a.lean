import Mathlib

open Set Real

theorem algebra_117403 {a : ℝ} (ha : 2 ≤ a) (A B C : Set ℝ)
    (hA : A = {x | -2 ≤ x ∧ x ≤ a}) (hB : B = {y | ∃ x ∈ A, y = 2 * x + 3})
    (hC : C = {t | ∃ x ∈ A, t = x ^ 2}) :
    C ⊆ B ↔ a ∈ Icc (1 / 2) 3 := by
  constructor
  · -- Assume C ⊆ B, prove a ∈ Icc (1 / 2) 3
    intro h 
    have h1 : a ≤ 3 := by 
      have h2 : a ^ 2 ∈ C := by 
        rw [hC]
        use a 
        constructor
        · -- Show that a is in A 
          rw [hA]
          exact ⟨by nlinarith, by linarith⟩ 
        · -- Show that a^2 = a^2 
          all_goals norm_num 
      have h3 : a ^ 2 ∈ B := h h2 
      rw [hB] at h3 
      rcases h3 with ⟨x, hx, h_eq⟩ 
      rw [hA] at hx 
      rcases hx with ⟨hx1, hx2⟩ 
      nlinarith [sq_nonneg (a - 3), sq_nonneg (x - a), sq_nonneg (a - 2)]
    constructor 
    · -- Show $1 / 2 \leq a$ 
      nlinarith 
    · -- Show $a \leq 3$ 
      linarith 
  · -- Assume a ∈ Icc (1 / 2) 3, prove C ⊆ B 
    intro h 
    rcases h with ⟨ha1, ha2⟩
    intro t ht 
    rw [hC] at ht 
    rcases ht with ⟨x, hx, ht⟩ 
    rw [hA] at hx 
    rcases hx with ⟨hx1, hx2⟩ 
    have h3 : t = x ^ 2 := by linarith 
    rw [h3] 
    rw [hB]
    use (x ^ 2 - 3) / 2 
    constructor
    · -- Show that the value is in A 
      rw [hA]
      constructor
      · -- Show it's ≥ -2 
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 3), sq_nonneg (x - a)]
      · -- Show it's ≤ a 
        nlinarith [sq_nonneg (x - a), sq_nonneg (x - 3), sq_nonneg (x + 2)]
    · -- Show that t = 2 * ((x ^ 2 - 3) / 2) + 3 
      nlinarith