import Mathlib

open scoped BigOperators

/-
Problem Analysis:
We need to determine the smallest positive integer n such that the probability of the townspeople winning against a goon exceeds 50%. The problem can be approached in two equivalent ways:
-/

theorem my_favorite_theorem 
    (p : ℕ → ℝ)
    (hp1 : p 1 = 1/3)
    (hpn : ∀ n ≥ 2, p n = 1/(2 * n + 1) + 2 * n / (2 * n + 1) * p (n - 1)) :
    IsLeast {n | 2 ≤ n ∧ p n > 1 / 2} 3 := by

  -- First, show that 3 is in the set {n | 2 ≤ n ∧ p n > 1/2}
  have h₁ : (3 : ℕ) ∈ {n | 2 ≤ n ∧ p n > 1 / 2} := by
    constructor

    -- Trivially, 3 ≥ 2
    · norm_num  

    · -- Compute p(3) step-by-step using the recurrence relation

      have h₂ := hpn 3 (by norm_num)  

      have h₃ := hpn 2 (by norm_num) 

      have h₄ : p 3 = 1/(2*3 +1) + (2*3/(2*3 +1)) * p 2 := by simpa 

      using h₂

      have h₅ : p 2 = 1/(2*2 +1) + (2*2/(2*2 +1)) * p 1 := by simpa

      using h₃
      
      have h₆ : p 1 = 1/3 := by simpa using hp1
      
      -- Verify p(3) > 1/2 through calculation
      norm_num [h₄, h₅, h₆]  

  -- Next, show 3 is the minimal element by proving no smaller n exists in the set

  refine' ⟨h₁, fun n hn => _⟩

  -- Split hn into its components: n ≥ 2 and p(n) > 1/2
  rcases hn with ⟨hn₁, hn₂⟩ 

  have h₂ : n ≥ 2 := hn₁  
  
  -- Since n is a natural number ≥2, it's either 2 or ≥3
  have h₃ : n ≥ 3 ∨ n = 2 := by omega  

  cases h₃ with

  -- If n ≥3, trivial; 3 is the least by default
  | inl h₃ => omega  

  -- Handle the case where n = 2 (show this leads to a contradiction)
  | inr h₃ =>  

    have h₄ : n = 2 := h₃

    -- Extract p(2) > 1/2 from hn₂
    have h₅ : p 2 > 1 / 2 := by simpa [h₄] using hn₂ 

    have h₆ : p 2 = 1/(2*2 +1) + (2*2/(2*2 +1)) * p 1 := by simpa using hpn 2 (by norm_num)

    have h₇ : p 1 = 1/3 := by simpa using hp1
    
    -- Compute p(2) = 7/15, which contradicts h₅ (p(2) > 1/2)
    norm_num [h₆, h₇] at h₅  