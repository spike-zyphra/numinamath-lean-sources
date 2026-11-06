import Mathlib

theorem number_theory_183299 (n p : ℕ) (hn: n = 101101101101)(hp: Nat.Prime p)(h:IsGreatest {p | p.Prime ∧ p ∣ n} p)(h2: 1000 ≤ p ∧ p ≤ 9999) : p = 9901 := by
  rw [hn] at h 
  have h1 : p ∈ {p | p.Prime ∧ p ∣ 101101101101} := by 
    exact h.1 
  rcases h1 with ⟨h_prime, hdiv⟩ 
  have h2' : ∀ q, q ∈ {p | p.Prime ∧ p ∣ 101101101101} → q ≤ p := by 
    apply h.2 
  -- Prove that p ≤ 9901 
  have h4 : p ≤ 9901 := by 
    by_contra h4 
    push_neg at h4 
    have h5 : p ≤ 9999 := h2.2 
    have h20 : p ∣ 101101101101 := hdiv 
    interval_cases p <;> norm_num at h_prime h20 <;> all_goals omega 
  -- Show 9901 is in the set 
  have h42 : 9901 ≤ p := by 
    have h51 : 9901 ∈ {p | p.Prime ∧ p ∣ 101101101101} := by 
      constructor 
      · norm_num 
      · norm_num 
    have h22 : 9901 ≤ p := by 
      have h22 : ∀ q, q ∈ {p | p.Prime ∧ p ∣ 101101101101} → q ≤ p := h.2 
      specialize h22 9901 (h51) 
      linarith 
    linarith 
  -- p = 9901 
  have h6 : p = 9901 := by 
    omega 
  exact h6