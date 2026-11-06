import Mathlib

def crossed_out (n : ℤ) := n ≥ 0

def circled (n : ℤ) := n ≤ 0

theorem number_theory_2012 (S : Set ℤ) (hS : ∀ n ∈ S, crossed_out n ∨ circled n)
    (hS' : ∃! n ∈ S, crossed_out n ∧ circled n) :
    0 ∈ S := by
  rcases hS' with ⟨n, hn1, hn2⟩
  have h1 : n ∈ S := hn1.1
  have h2 : crossed_out n := hn1.2.1
  have h3 : circled n := hn1.2.2
  have h4 : n ≥ 0 := by 
    simpa using h2
  have h5 : n ≤ 0 := by 
    simpa using h3
  have hn0 : n = 0 := by 
    omega 
  rw [hn0] at h1
  exact h1