import Mathlib

open Real Int Nat Set
open scoped BigOperators

theorem algebra_14031 {f : ℝ → ℝ}
  (hf : ∀ x, f x = 3 ^ x / (3 ^ x + 1) - 1 / 3) :
  range (λ x => ⌊f x⌋) = {0, -1} := by
    ext n
    simp only [mem_range, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · -- First direction: if n ∈ range of ⌊f(x)⌋, then n ∈ {0, -1}
      intro hn
      rcases hn with ⟨x, hx⟩
      have h1 : 0 ≤ (3 : ℝ) ^ x := by positivity
      have h2 : 0 < (3 : ℝ) ^ x + 1 := by nlinarith
      have h3 : f x > -1 / 3 := by 
        rw [hf x]
        have h4 : (3 : ℝ) ^ x / ((3 : ℝ) ^ x + 1) > 0 := by positivity
        linarith
      have h4 : f x < 2 / 3 := by 
        rw [hf x]
        have h5 : (3 : ℝ) ^ x / ((3 : ℝ) ^ x + 1) < 1 := by
          apply (div_lt_iff (by positivity)).mpr
          nlinarith
        linarith
      have h5 : ⌊f x⌋ = 0 ∨ ⌊f x⌋ = -1 := by 
        have h6 : -1 / 3 < f x := by linarith
        have h7 : f x < 2 / 3 := by linarith
        by_cases h : f x ≥ 0 
        · -- If f(x) ≥ 0, then floor(f(x)) = 0
          have h9 : ⌊f x⌋ = 0 := by 
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> nlinarith
          left 
          exact h9
        · -- If f(x) < 0, then floor(f(x)) = -1 
          have h10 : ⌊f x⌋ = -1 := by 
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> nlinarith
          right 
          exact h10
      rw [hx] at h5 
      tauto 
    · -- Second direction: {0, -1} ⊆ range of ⌊f(x)⌋ 
      rintro (h | h)
      · -- Existential witness x = 0 for 0 
        use (0 : ℝ)
        rw [hf]
        norm_num
        <;> omega 
      · -- Existential witness x = -1 for -1 
        use (-1 : ℝ)
        rw [hf]
        norm_num
        <;> omega