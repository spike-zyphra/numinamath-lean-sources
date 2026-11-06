import Mathlib

/-
Theorem: The sum of (p-1) for all integers from 1 to N divisible by prime p equals (p-1) times the quotient of N divided by p.
-/
theorem Number_Theory_638987
    (N : ℕ) 
    (p : ℕ) :
    (∑ i in Finset.Icc 1 N, 
    (if p ∣ i then p - 1 else 0 : ℕ))
     = (p - 1) * (N / p) := by

  -- Helper lemma: Identity function for the summand
  have h₁ : ∀ n : ℕ, n ∈ Finset.Icc 1 N → (if p ∣ n then p - 1 else 0 : ℕ) = (if p ∣ n then p - 1 else 0 : ℕ) := by
    intro n hn
    rfl
  calc

    -- Initial equality by reflexivity
    (∑ i in Finset.Icc 1 N, (if p ∣ i then p - 1 else 0 : ℕ)) = ∑ i in Finset.Icc 1 N, (if p ∣ i then p - 1 else 0 : ℕ) := rfl
    _ = (p - 1) * (N / p) := by

      -- Main proof step
      have h₂ : (∑ i in Finset.Icc 1 N, (if p ∣ i then p - 1 else 0 : ℕ)) = (p - 1) * (N / p) := by

        -- Inductive proof over natural numbers
        have h₃ : ∀ k : ℕ, (∑ i in Finset.Icc 1 k, (if p ∣ i then p - 1 else 0 : ℕ)) = (p - 1) * (k / p) := by
          intro k
          
          -- Strong induction hypothesis
          have h₄ : ∀ m : ℕ, (∑ i in Finset.Icc 1 m, (if p ∣ i then p - 1 else 0 : ℕ)) = (p - 1) * (m / p) := by
            intro m
            induction m with
            | zero =>
              simp [Finset.sum_range_zero]
            | succ m ih =>
              rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m.succ), ih]

              -- Case analysis: whether p divides the current number
              by_cases h₅ : p ∣ m.succ

              · -- Case 1: p divides m.succ
                have h₆ : p ∣ m.succ := h₅
                have h₇ : p ∣ m.succ := h₅

                -- Simplify the if-then-else expression
                have h₈ : (if p ∣ m.succ then p - 1 else 0 : ℕ) = p - 1 := by
                  simp [h₇]
                rw [h₈]

                -- Apply division lemma for multiples of p
                have h₉ : m.succ / p = m / p + 1 := by
                  have h₁₀ : p ∣ m.succ := h₅
                  have h₁₁ : m.succ / p = m / p + 1 := by
                    have h₁₂ : p ∣ m.succ := h₅
                    have h₁₃ : m.succ / p = m / p + 1 := by
                      exact Nat.succ_div_of_dvd h₅
                    exact h₁₃
                  exact h₁₁
                rw [h₉]

                -- Simplify the arithmetic expression
                ring_nf 

              · -- Case 2: p does not divide m.succ
                have h₆ : ¬p ∣ m.succ := h₅
                have h₇ : ¬p ∣ m.succ := h₅

                -- Simplify the if-then-else expression
                have h₈ : (if p ∣ m.succ then p - 1 else 0 : ℕ) = 0 := by
                  simp [h₇]
                rw [h₈]

                -- Apply division lemma for non-multiples of p
                have h₉ : m.succ / p = m / p := by
                  have h₁₀ : ¬p ∣ m.succ := h₅
                  have h₁₁ : m.succ / p = m / p := by
                    have h₁₂ : ¬p ∣ m.succ := h₅
                    have h₁₃ : m.succ / p = m / p := by
                      exact Nat.succ_div_of_not_dvd h₅
                    exact h₁₃
                  exact h₁₁
                rw [h₉]

                -- Simplify the arithmetic expression
                ring_nf 
          exact h₄ k
        have h₄ : (∑ i in Finset.Icc 1 N, (if p ∣ i then p - 1 else 0 : ℕ)) = (p - 1) * (N / p) := by
          have h₅ : (∑ i in Finset.Icc 1 N, (if p ∣ i then p - 1 else 0 : ℕ)) = (p - 1) * (N / p) := by
            apply h₃
          exact h₅
        exact h₄
      exact h₂

    -- Final equality by reflexivity
    _ = (p - 1) * (N / p) := by rfl  