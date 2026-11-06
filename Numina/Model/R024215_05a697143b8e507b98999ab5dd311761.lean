import Mathlib

theorem number_theory_209330 (S : Finset ℕ) (hS : S.card ≤ 14)
    (hS1 : ∑ x ∈ S, x ^ 4 = 1599) :
    False := by 
  have h1 : ∀ x ∈ S, x ≤ 6 := by 
    intro x hx 
    by_contra h 
    push_neg at h 
    have h2 : x ≥ 7 := by omega 
    have h3 : x ^ 4 ≥ 2401 := by 
      have h4 : x ≥ 7 := by omega 
      have h5 : x ^ 4 ≥ 7 ^ 4 := by 
        apply Nat.pow_le_pow_of_le_left 
        omega 
      norm_num at h5 ⊢ 
      linarith 
    have h4 : ∑ x in S, x ^ 4 ≥ x ^ 4 := by 
      apply Finset.single_le_sum (fun i hi => by simp) (show x ∈ S by exact hx) 
    linarith 
  have h2 : S ⊆ Finset.Icc 0 6 := by 
    intro x hx 
    simp at *
    have h1' : x ≤ 6 := h1 x hx 
    omega 
  have h3 : S ∈ (Finset.powerset (Finset.Icc 0 6)).filter (fun s => s.card ≤ 14) := by 
    simp [Finset.mem_powerset, h2, hS] 
  have h5 : ∀ s ∈ (Finset.powerset (Finset.Icc 0 6)).filter (fun s => s.card ≤ 14), (∑ x in s, x ^ 4) ≠ 1599 := by 
    native_decide 
  specialize h5 S h3 
  contradiction