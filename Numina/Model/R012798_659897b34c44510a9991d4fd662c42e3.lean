import Mathlib

theorem number_theory_8378 :
    Set.ncard {n : ℕ | n < 500 ∧ (Nat.divisors n).card = 15} = 3 := by
  have h1 : {n : ℕ | n < 500 ∧ (Nat.divisors n).card = 15} = Finset.filter (fun n => n < 500 ∧ (Nat.divisors n).card = 15) (Finset.Icc 0 499) := by
    ext n
    simp
    <;> try { 
      apply Iff.intro
      · -- Assume (n < 500 ∧ (Nat.divisors n).card = 15), prove the right side
        intro h
        rcases h with ⟨h1, h2⟩
        constructor 
        · -- Prove n ≤ 499
          omega 
        · -- Prove n < 500 ∧ (Nat.divisors n).card = 15
          tauto 
      · -- Assume right side: n ≤ 499 ∧ n < 500 ∧ (Nat.divisors n).card = 15, prove left side
        intro h
        rcases h with ⟨h1, h2⟩ 
        tauto 
    }
    <;> try { omega } 
    <;> try { tauto } 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide