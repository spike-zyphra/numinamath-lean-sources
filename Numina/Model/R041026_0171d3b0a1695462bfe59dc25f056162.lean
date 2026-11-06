import Mathlib

theorem algebra_233407 :
    {x : ℕ | x > 0 ∧ ∑ i in Finset.Icc 1 x, i^4 = ∑ i in Finset.Icc 1 x, i + ∑ i in Finset.Icc 1 x, i^2 + ∑ i in Finset.Icc 1 x, i^3} = {2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if x is in the left side, then it must be in the right side.
    intro h
    rcases h with ⟨hx_pos, heq⟩
    have h1 : x > 0 := hx_pos
    have h1_le : x ≤ 4 := by
      by_contra h
      push_neg at h
      have h2' : x ≥ 5 := by omega
      have h2 : ∑ i in Finset.Icc 1 x, i ^ 4 > ∑ i in Finset.Icc 1 x, i + ∑ i in Finset.Icc 1 x, i ^ 2 + ∑ i in Finset.Icc 1 x, i ^ 3 := by
        have h11 : ∀ (x : ℕ), x ≥ 5 → ∑ i in Finset.Icc 1 x, i ^ 4 > ∑ i in Finset.Icc 1 x, i + ∑ i in Finset.Icc 1 x, i ^ 2 + ∑ i in Finset.Icc 1 x, i ^ 3 := by
          intro y hy2
          have base5 : ∑ i in Finset.Icc 1 5, i ^ 4 > ∑ i in Finset.Icc 1 5, i + ∑ i in Finset.Icc 1 5, i ^ 2 + ∑ i in Finset.Icc 1 5, i ^ 3 := by 
            norm_num [Finset.sum_Icc_succ_top]
          have step5 : ∀ (x : ℕ), x ≥ 5 → (∑ i in Finset.Icc 1 x, i ^ 4 > ∑ i in Finset.Icc 1 x, i + ∑ i in Finset.Icc 1 x, i ^ 2 + ∑ i in Finset.Icc 1 x, i ^ 3) → 
          ∑ i in Finset.Icc 1 (x + 1), i ^ 4 > ∑ i in Finset.Icc 1 (x + 1), i + ∑ i in Finset.Icc 1 (x + 1), i ^ 2 + ∑ i in Finset.Icc 1 (x + 1), i ^ 3 := by 
            intro x h4 ih4
            have eq3 : ∑ i in Finset.Icc 1 (x + 1), i ^ 4 = ∑ i in Finset.Icc 1 x, i ^ 4 + (x + 1) ^ 4 := by 
              rw [Finset.sum_Icc_succ_top (by linarith)]
            have eq4 : ∑ i in Finset.Icc 1 (x + 1), i + ∑ i in Finset.Icc 1 (x + 1), i ^ 2 + ∑ i in Finset.Icc 1 (x + 1), i ^ 3 = (∑ i in Finset.Icc 1 x, i + ∑ i in Finset.Icc 1 x, i ^ 2 + ∑ i in Finset.Icc 1 x, i ^ 3) + (x + 1) + (x + 1) ^ 2 + (x + 1) ^ 3 := by 
              simp [Finset.sum_Icc_succ_top]
              <;> ring_nf <;> omega
            rw [eq3, eq4]
            nlinarith [show (x + 1: ℕ) ^ 4 ≥ (x + 1) + (x + 1) ^ 2 + (x + 1) ^ 3 by nlinarith [sq_nonneg ((x + 1 : ℕ) : ℕ), sq_nonneg ((x + 1 : ℕ) + 1 : ℕ), sq_nonneg ((x + 1 : ℕ) ^ 2 : ℕ), sq_nonneg ((x + 1 : ℕ) ^ 3 : ℕ) ] ]
          exact Nat.le_induction base5 step5 y hy2
        exact h11 x h2'
      linarith [h2, heq]
      all_goals omega
    interval_cases x <;> try { norm_num [Finset.sum_Icc_succ_top] at heq ⊢ <;> all_goals tauto <;> try { 
      exfalso
      all_goals try { trivial }
    }
  }
    <;> try { trivial }
    <;> try { 
      exfalso
      all_goals try { trivial }
    }
    <;> try { 
      exfalso
      all_goals try { 
        tauto
      }
    }
    <;> try { 
      exfalso
      all_goals try { 
        tauto
      }
    }
    <;> try { 
      exfalso
      all_goals try { 
        trivial
      }
    }
    <;> try { 
      exfalso
      all_goals try { 
        trivial
      }
    }
  · -- Proof in the reverse direction
    intro h
    rw [h]
    constructor
    · norm_num
    · -- Verify that 2 satisfies the equation
      norm_num [Finset.sum_Icc_succ_top]
      <;> try { native_decide }
      <;> tauto