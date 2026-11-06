import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem algebra_279645 {G : Type*} [Group G] [Fintype G]
  (hG : card G > 1) :
  (card G).totient ≤ card G ∧ card G ≤ (card G).divisors.sum id := by
  constructor
  · -- First goal: show that (card G).totient ≤ card G 
    have h1 : (card G).totient ≤ card G := by 
      apply Nat.totient_le 
      all_goals linarith
    exact h1
  · -- Second goal: show that card G ≤ (card G).divisors.sum id 
    have h2 : card G ≤ (card G).divisors.sum id := by 
      have h3 : card G ∈ (card G).divisors := by 
        have h4 : card G ∣ card G := by 
          exact dvd_refl (card G)
        simp [Finset.mem_insert, Finset.mem_singleton] at *
        <;> tauto 
      have h5 : (card G).divisors.sum id ≥ card G := by 
        have h6 : card G ∈ (card G).divisors := h3
        have h9 : id (card G) ≤ (card G).divisors.sum id := by 
          apply Finset.single_le_sum (fun i hi => by 
            have h10 : (id i : ℕ) ≥ 0 := by 
              simp 
            simpa using h10 
          ) h6 
        simp at h9 ⊢ 
        all_goals linarith 
      linarith
    exact h2