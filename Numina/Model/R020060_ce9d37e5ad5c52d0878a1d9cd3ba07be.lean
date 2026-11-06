import Mathlib

theorem number_theory_241045 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 2000 3000 ∧ ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ 2 * p = 5 * q ∧ p + q = n} = 143 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 2000 3000 ∧ ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ 2 * p = 5 * q ∧ p + q = n} = 
    {n | n ∈ Finset.Icc 2000 3000 ∧ n % 7 = 0} := by
    ext n 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, and_imp]
    constructor
    · -- Assume n in the original set.
      rintro ⟨⟨hn1, hn2⟩, p, q, hp, hq, h1, h2⟩
      have h2 : ∃ k : ℕ, n = 7 * k := by
        have h3 : (n) % 7 = 0 := by 
          omega
        have : n % 7 = 0 := h3 
        refine ⟨n / 7, by omega⟩ 
      rcases h2 with ⟨k, hk⟩ 
      omega
    · -- Assume n in RHS.
      rintro ⟨⟨hn1, hn2⟩, h⟩ 
      constructor
      · -- Show n in Icc.
        exact ⟨by omega, by omega⟩ 
      · -- Show existence of p and q.
        use (5 * (n / 7)), (2 * (n / 7))
        all_goals 
          omega
  rw [h1]
  have h4 : {n | n ∈ Finset.Icc 2000 3000 ∧ n % 7 = 0} = Finset.filter (fun (n: ℕ) => n % 7 = 0) (Finset.Icc 2000 3000) := by 
    ext n 
    simp 
    <;> tauto
  rw [h4] 
  rw [Set.ncard_coe_Finset]
  native_decide