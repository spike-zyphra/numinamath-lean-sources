import Mathlib
open Finset Set Nat 
noncomputable section

def pascal (n k : Nat) : Int :=
  if k > n then 0
  else if n = 0 then (if k = 0 then 1 else 0)
  else if k = 0 then 1
  else if k = n then 1
  else pascal (n - 1) k - pascal (n - 1) (k - 1)

/-Pascal has a triangle. In the $n$th row, there are $n+1$ numbers $a_{n, 0}, a_{n, 1}, a_{n, 2}, \ldots, a_{n, n}$ where $a_{n, 0}=a_{n, n}=1$. For all $1 \leq k \leq n-1, a_{n, k}=a_{n-1, k}-a_{n-1, k-1}$. What is the sum of all numbers in the 2018th row?-/
theorem combinatorics_2345678 : (∑ k ∈ Finset.range (2018 + 1), pascal 2018 k) = 2 := by
  -- proposition: For any $n ≥ 1$, the sum of the nth row is $2$.
  have h_row_sum : ∀ n, n ≥ 1 → (∑ k ∈ Finset.range (n + 1), pascal n k) = 2 := by
    intro n hn
    cases n with
    | zero =>
      have : 0 ≥ 1 → False := by simp
      linarith
    | succ m =>
      -- $n = m + 1$, $m ≥ 0$.
      induction m with
      | zero =>
        -- Base case: $n = 1$.
        have h_pascal_1_0 : pascal 1 0 = 1 := by simp [pascal]
        have h_pascal_1_1 : pascal 1 1 = 1 := by simp [pascal]
        have h_pascal_1_k : ∀ k ≥ 2, pascal 1 k = 0 := by
          unfold pascal
          intros k hk
          simp
          omega
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        simp [h_pascal_1_0, h_pascal_1_1, h_pascal_1_k]
      | succ m ih =>
        -- Induction step: $n = (m + 1) + 1$, $m ≥ 0$.
        let n := m + 2
        have h_split_sum : (∑ k ∈ Finset.range (n + 1), pascal n k) =
                  pascal n 0 + (∑ k ∈ Finset.range (n - 1), pascal n (k + 1)) + pascal n n := by
          -- Split into $k=0$, $k=1$ to $n-1$, $k=n$.
          have : n - 1 = m + 1 := by omega
          rw [this]
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ']
          linarith
        have h_first_term : pascal n 0 = 1 := by
          -- Prove $a_{n,0} = 1$.
          simp [pascal, n]
        have h_middle_sum : (∑ k ∈ Finset.range (n - 1), pascal n (k + 1)) =
                  ∑ k ∈ Finset.range (n - 1), (pascal (m + 1) (k + 1) - pascal (m + 1) k) := by
          -- Apply recursive relation.
          have : ∀ k ∈ Finset.range (n - 1),
            pascal n (k + 1) = pascal (m + 1) (k + 1) - pascal (m + 1) k := by
            intros k hk
            have : k < n - 1 := by simp [Finset.mem_range] at hk; exact hk
            have : k + 1 < n := by omega
            have : k + 1 ≠ 0 := by linarith
            have : k + 1 ≠ n := by linarith
            have : n ≠ 0 := by simp [n]
            have h_rec : pascal n (k + 1) = pascal (m + 1) (k + 1) - pascal (m + 1) k := by
              -- Unfold the left side of the equation.
              conv_lhs =>
                unfold pascal
              rw [if_neg (by linarith)]
              rw [if_neg this]
              rw [if_neg (by linarith)]
              rw [if_neg (by linarith)]
              have : n - 1 = m + 1 := by simp [n]
              rw [this]
              rfl
            exact h_rec
          rw [Finset.sum_congr rfl this]
        have h_last_term : pascal n n = 1 := by
          -- Prove $a_{n,n} = 1$.
          simp [pascal, n]
        have h_diff_sum : (∑ k ∈ Finset.range (n - 1), (pascal (m + 1) (k + 1) - pascal (m + 1) k)) =
                  pascal (m + 1) (n - 1) - pascal (m + 1) 0 := by
          -- Compute the sum of differences as a telescoping sum.
          have h_telescope : ∀ (n : ℕ), (∑ k ∈ Finset.range n, (pascal (m + 1) (k + 1) - pascal (m + 1) k)) = pascal (m + 1) n - pascal (m + 1) 0 := by
            intro n
            induction n with
            | zero =>
              unfold pascal; simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              unfold pascal
              simp [Nat.succ_eq_add_one] at *
          have h_n_minus_1 : n - 1 = m + 1 := by omega
          rw [h_n_minus_1]
          have h_apply_telescope : (∑ k ∈ Finset.range (m + 1), (pascal (m + 1) (k + 1) - pascal (m + 1) k)) = pascal (m + 1) (m + 1) - pascal (m + 1) 0 := by
            apply h_telescope
          simpa [h_n_minus_1] using h_apply_telescope
        have h_penultimate : pascal (m + 1) (n - 1) = 1 := by
          -- Prove $a_{m+1,m+1} = 1$.
          simp [pascal, n]
        have h_first_m : pascal (m + 1) 0 = 1 := by
          -- Prove $a_{m+1,0} = 1$.
          simp [pascal]
        have h_final_sum : (∑ k ∈ Finset.range (n + 1), pascal n k) = 2 := by
          -- Combine all subgoals.
          rw [h_split_sum, h_first_term, h_middle_sum, h_last_term, h_diff_sum, h_penultimate, h_first_m]
          simp
        exact h_final_sum
  -- Substitute $n = 2018$.
  exact h_row_sum 2018 (by linarith)
