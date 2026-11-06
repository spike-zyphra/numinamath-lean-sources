import Mathlib

open Finset

/-
Problem:
For this problem, our lawn consists of a row of n clumps of grass. This row runs in an east-west direction. In our formation, each mobot may be oriented toward the north, south, east, or west. One example of an allowable formation if n=6 is symbolized below
-/
theorem combinatorics_611521 
    {n : ℕ} :
    ∑ a ∈ Icc 0 n , 
    ∑ b ∈ Icc 0 (n - a) , 
    2 ^ (n - a - b) = 2 ^ (n + 2) - n - 3 := by

  -- First, transform the inner summation over b into a closed-form expression
  have t₁ : ∑ a in Icc 0 n, (∑ b in Icc 0 (n - a) , 2 ^ (n - a - b)) = ∑ a in Icc 0 n , (2 ^ (n - a + 1) - 1) := by

    -- Prove that for any a in [0, n], the inner sum equals 2^(n - a + 1) - 1
    have h₁ : ∀ a ∈ Icc 0 n , (∑ b in Icc 0 (n - a) , 2 ^ (n - a - b)) = 2 ^ (n - a + 1) - 1 := by
      intro a ha

      -- Extract the fact that a ≤ n from the hypothesis
      have h₂ : a ≤ n := Finset.mem_Icc.mp ha |>.2
      have t₁₁ : ∑ b in Icc 0 (n - a) , 2 ^ (n - a - b) = 2 ^ (n - a + 1) - 1 := by

        -- Convert the interval [0, n-a] to the range [0, n-a+1)
        have h₁ : ∑ b in Icc 0 (n - a) , 2 ^ (n - a - b) = ∑ b in range (n - a + 1) , 2 ^ (n - a - b) := by
          apply sum_bij (fun (b : ℕ) _ => b)
          <;> simp_all [mem_Icc, mem_range, Nat.lt_succ_iff]
        rw [h₁]

        -- Change the summation index to reverse the order
        have h₂ : ∑ b in range (n - a + 1) , 2 ^ (n - a - b) = ∑ k in range (n - a + 1) , 2 ^ k := by
          apply sum_bij' (fun b _ => n - a - b) (fun k _ => n - a - k)
          <;> simp_all 
          [mem_range, Nat.lt_succ_iff, Nat.sub_add_comm, Nat.sub_sub_self, Nat.le_sub_of_add_le]
        rw [h₂]

        -- Prove that the sum of 2^k from 0 to m is 2^(m+1) - 1 by induction
        have h₃ : ∑ k in range (n - a + 1) , 2 ^ k = 2 ^ (n - a + 1) - 1 := by
          induction' (n - a) with m ih
          · simp
          · have h₄ : ( ∑ k in range (m + 1 + 1) , 2 ^ k) = ∑ k in range (m + 1) , 2 ^ k + 2 ^ (m + 1) := by 
              exact
              sum_range_succ (HPow.hPow 2) (m + 1)
            rw [h₄ , ih]
            have h₅ : 2 ^ (m + 1) - 1 + 2 ^ (m + 1) = 2 * 2 ^ (m + 1) - 1 := by 
              exact Nat.sub_one_add_self (2 ^ (m + 1))
            rw [h₅]
            have h₆ : 2 * (2 ^ (m + 1)) - 1 = 2 ^ (m + 1 + 1) - 1 := by ring_nf
            rw [h₆]
        rw [h₃]
      exact t₁₁
    rw [Finset.sum_congr rfl h₁]

  -- Split the summation into two separate sums
  have t₂ : (∑ a ∈ Icc 0 n , (2 ^ (n - a + 1) - 1)) = (∑ a ∈ Icc 0 n , (2 ^ (n - a + 1))) - (n + 1) := by 

    -- Apply the distributive property of summation over subtraction
    have t₂₁ : (∑ a ∈ Icc 0 n , (2 ^ (n - a + 1) - 1)) = (∑ a ∈ Icc 0 n, (2 ^ (n - a + 1)))-(∑ a ∈ Icc 0 n , 1) := by 
      refine sum_tsub_distrib (Icc 0 n)
       (by exact fun x a => Nat.one_le_two_pow)

    -- Compute the sum of 1 from 0 to n, which is n+1
    have t₂₂ : (∑ a ∈ Icc 0 n , 1) = (n + 1) := by 
      simp_all [Finset.sum_const, add_comm]
    rw [t₂₁ , t₂₂]

  -- Compute the closed-form of the remaining summation
  have t₃ : ∑ a ∈ Icc 0 n, (2 ^ (n - a + 1)) = 2 ^ (n + 2) - 2 := by

    -- Convert the interval [0, n] to the range [0, n+1)
    have h₁ : ∑ a ∈ Icc 0 n, 2 ^ (n - a + 1) = ∑ a ∈ range (n + 1) , 2 ^ (n - a + 1) := by
      apply Finset.sum_bij' (fun a _ => a) (fun a _ => a) <;> simp_all [Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
    rw [h₁]

    -- Prove that the summation equals 2^(n+2) - 2
    have h₂ : ∑ a ∈ range (n + 1), 2 ^ (n - a + 1) = 2 ^ (n + 2) - 2 := by
      have h₃ : ∀ n : ℕ, ∑ a ∈ range (n + 1), 2 ^ (n - a + 1) = 2 ^ (n + 2) - 2 := by
        intro n

        -- Change the summation index to reverse the order
        have h₄ : ∑ a ∈ range (n + 1) , 2 ^ (n - a + 1) = ∑ k ∈ range (n + 1) , 2 ^ (k + 1) := by
          apply Finset.sum_bij' (fun a _ => n - a) (fun a _ => n - a)
          <;> simp_all [Finset.mem_range, Nat.lt_succ_iff, Nat.sub_add_comm, Nat.add_sub_cancel]
          <;> omega
        rw [h₄]

        -- Prove the summation identity using properties of exponents
        have h₅ : ∑ k ∈ range (n + 1) , 2 ^ (k + 1) = 2 ^ (n + 2) - 2 := by
          have h₆ : ∑ k ∈ range (n + 1) , 2 ^ (k + 1) = (∑ k ∈ range (n + 1) , 2 ^ (k + 1)) := rfl
          rw [h₆]
          have h₇ : ∑ k ∈ range (n + 1) , 2 ^ (k + 1) = 2 ^ (n + 2) - 2 := by

            -- Rewrite 2^(k+1) as 2 * 2^k
            rw [show (∑ k ∈ range (n + 1) , 2 ^ (k + 1)) = ∑ k ∈ range (n + 1) , 2 * 2 ^ k by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show 2 ^ (k + 1) = 2 * 2 ^ k by
                simp [pow_succ, mul_comm]]]

            -- Use the formula for the sum of a geometric series
            have h₈ : ∀ n : ℕ, ∑ k ∈ range n , (2 : ℕ) ^ k = 2 ^ n - 1 := by 
              intro n 
              have h₁ : ∑ k ∈ range n , (2 : ℕ) ^ k = 2 ^ n - 1 := by  
                induction n with 
                | zero => simp 
                | succ n ih => 
                  rw [Finset.sum_range_succ, ih] 
                  simp [Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc] 
                  ring_nf at * 
                  omega
              exact h₁

            -- Factor out the constant 2 from the summation
            have m₁ : ∑ k ∈ range (n + 1) , 2 * 2 ^ k = 2 * ∑ k ∈ range (n + 1) , 2 ^ k := by 
              exact
              Eq.symm (mul_sum (range (n + 1)) (HPow.hPow 2) 2)
            rw [m₁ , h₈]

            -- Simplify the expression using arithmetic properties
            have h₉ : 2 * (2 ^ (n + 1) - 1) = 2 ^ (n + 2) - 2 := by
              cases n with
              | zero => simp
              | succ n =>
                simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
                ring_nf at *
            rw [h₉]
          rw [h₇]
        rw [h₅]
      exact h₃ n
    rw [h₂]

  -- Substitute the result of t₃ into t₂
  rw [t₃] at t₂

  -- Simplify the final expression using arithmetic properties
  have t₄ : 2 ^ (n + 2) - 2 - (n + 1) = 2 ^ (n + 2) - n - 3 := by 
    exact Nat.sub_right_comm (2 ^ (n + 2)) 2 (n + 1)
    
  -- Conclude the proof using linear arithmetic
  linarith