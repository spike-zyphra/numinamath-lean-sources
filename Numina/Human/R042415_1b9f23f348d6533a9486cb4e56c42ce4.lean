import Mathlib
set_option exponentiation.threshold 5000
--maximum value for which exponentiation operations are safe to evaluate.

/-Let f be a function  with the following properties
(i) f(1) = 1 and
(ii) f(2n)= n ⬝ f(n) for any positive integer n.
What is the value of f(2^100)?
(A)1 (B)2^99 (C)2^100 (D)2^4950 (E)2^9999
-/

theorem algebra_95206  {f : ℕ → ℕ}
(h1 : f 1 = 1) (h2 : ∀ n > 0, f (2 * n) = n * f n) : f (2 ^ 100) = 2 ^ 4950 := by

have h : ∀ n : ℕ, f (2^n) = 2^((n-1) * n / 2) := by
    intro n
    induction n with
    | zero =>
        -- Base case: f(2^0) = f(1) = 1
        rw [pow_zero] --a^0 =1 for all a
        exact h1 -- uses h1
    | succ n ih =>
        -- inductive step
        calc
        f (2 ^ (n + 1))
          = f (2 * 2 ^ n) := by
                rw [pow_succ, mul_comm]
        _ = (2 ^ n) * f (2 ^ n) := by
                apply h2
                --uses the assumption h2
                apply pow_pos
                --shows 2>0
                norm_num
                --normalizes numerical expressions
        _ = (2 ^ n) * (2 ^ ((n - 1) * n / 2)) := by
                rw [ih]
                --uses the inductive hypothesis
        _ = 2 ^ (n + ((n - 1) * n / 2)) := by
                ring_nf
                --simplifying using ring_nf
        _ = 2 ^ (((n + 1 - 1) * (n + 1)) / 2) := by
                      congr
                      --ensures both sides are structurally same
                      symm
                      nth_rewrite 1 [mul_comm]
                      --apply tactic to 1st occurrence etc
                      nth_rewrite 2 [mul_comm]
                      nth_rewrite 2 [add_comm]
                      apply Nat.div_eq_of_eq_mul_right
                      --expresses division in form of multiplication
                      simp
                      --simplifies expression
                      rw [mul_add]
                      --expands product over addition
                      cases n with
                      --case analysis
                      | zero => simp
                      | succ n =>
                        simp
                        have : 2 * ((n + 1) * n / 2) = (n+1) * n := by
                                nth_rewrite 1 [mul_comm]
                                --Swap multiplication order in first occurrence
                                refine Nat.div_two_mul_two_of_even ?_
                                --property that division by 2 is valid when even
                                refine Nat.even_mul.mpr ?_
                                --`(n + 1) * n` is even
                                by_cases H : Even n
                                --either `n` is even or it is odd
                                · tauto
                                · left
                                  exact Nat.even_add_one.mpr H
                                  --if n is odd then n+1 is even
                        rw [this]
                        --rewrite using proven equality
                        linarith
                        --finishes goal


exact h 100
--this completes the proof