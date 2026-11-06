import Mathlib

open Finset

theorem number_theory_47680 {f g : ℕ → ℕ}
    (hf : ∀ n, f (n + 1) = ∑ d ∈ (n + 1).divisors, f d)
    (hg : ∀ n, g (n + 1) = ∑ d ∈ (n + 1).divisors, g d) :
    ∃ m, ∃ n, f m = g n := by

  have h1 := hf 1
  have h2 := hg 1
  
  -- From $f(2) = \sum_{d \in 2.divisors} f(d)$, since 2 is {1, 2}, we get f(2) = f(1) + f(2), so f(1) = 0
  have h3 : f 1 = 0 := by 
    have h1' := hf 1 
    have h4 : f 2 = ∑ d ∈ (2 : ℕ).divisors, f d := by 
      simpa using h1' 
    have h5 : (2 : ℕ).divisors = {1, 2} := by 
      native_decide 
    rw [h5] at h4 
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton] at h4 
    omega 
  -- From $g(2) = \sum_{d \in 2.divisors} g(d)$, we get g(2) = g(1) + g(2), so g(1) = 0
  have h4 : g 1 = 0 := by 
    have h2' := hg 1 
    have h5 : g 2 = ∑ d ∈ (2 : ℕ).divisors, g d := by 
      simpa using h2' 
    have h6 : (2 : ℕ).divisors = {1, 2} := by 
      native_decide 
    rw [h6] at h5 
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton] at h5 
    omega 
  exact ⟨1, 1, by simp [h3, h4]⟩