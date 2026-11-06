import Mathlib
set_option maxRecDepth 3000

open Finset

/-For any positive integer $n$, let $f(n)$ denote the number of 1 's in the base- 2 representation of $n$. For how many values of $n$ with $1 \leq n \leq 2002$ do we have $f(n)=f(n+1)$ ?-/
theorem number_theory_610978 (f : ℕ → ℕ) (hf : ∀ n > 0, f n =
    List.count 1 (Nat.digits 2 n)) : #{n ∈ Icc 1 2002| f n = f (n + 1)} = 501 := by
-- It suffices to show that the set in question is equal to the set of all numbers modulo $4$ equal to $1$   
  suffices : {n ∈ Icc 1 2002 | f n = f (n + 1)} = {n ∈ Icc 1 2002| n % 4 = 1}
  · rw [this]; decide
-- Prove that $n+1$ has at most one more $1$'s in the base-$2$ representations, we proceed by strong parity induction
  have aux : ∀ n > 0, (f (n + 1) : ℤ) - f n ≤ 1 := by
    intro n npos; induction n using Nat.evenOddStrongRec with
    | h_even n _ =>
      rw [hf, hf, add_comm]; nth_rw 2 [show 2*n = 0+2*n by simp]
      repeat rw [Nat.digits_add, List.count_cons]
      any_goals simp
      all_goals omega
    | h_odd n ihn =>
      by_cases h : n ≤ 0
      · simp at h; simp [h, hf]
      rw [hf, hf, show 2*n+1+1 = 0+2*(n+1) by ring]
      nth_rw 3 [add_comm]; repeat rw [Nat.digits_add, List.count_cons]
      simp [← Nat.digits_of_two_le_of_pos]
      specialize ihn n (by omega) (by omega)
      rw [hf, hf] at ihn; all_goals omega
  simp [Finset.ext_iff]; intro n npos _; constructor
  -- Split to all possible remainders modulo $4$
  · intro hfn; have := Nat.mod_lt n (show 4>0 by simp)
    interval_cases mod4 : n % 4
    -- In the even cases, $n$'s last digit is $0$, therefore $n+1$ will have one more $1$ in the base-2 representation
    · rw [hf, hf] at hfn
      simp [show (n+1)%2 = 1 by omega] at hfn
      rw [show (n+1)/2 = n/2 by omega] at hfn
      nth_rw 1 [show n = 0+2*(n/2) by omega] at hfn
      rw [Nat.digits_add, List.count_cons] at hfn
      simp at hfn; all_goals omega
    · rfl
    · rw [hf, hf] at hfn
      simp [show (n+1)%2 = 1 by omega] at hfn
      rw [show (n+1)/2 = n/2 by omega] at hfn
      nth_rw 1 [show n = 0+2*(n/2) by omega] at hfn
      rw [Nat.digits_add, List.count_cons] at hfn
      simp at hfn; all_goals omega
  -- The $4*t+3$ cases is dealt by rewriting `hfn` to $f(k)+2=f(k+1)$ for some $k$, which contradicts to `aux`
    rw [hf, hf] at hfn
    simp [show (n+1)%2 = 0 by omega] at hfn
    rw [show (n+1)/2 = 0+2*((n+1)/4) by omega] at hfn
    nth_rw 1 [show n = 1+2*((n-1)/2) by omega] at hfn
    repeat rw [Nat.digits_add] at hfn
    rw [show (n+1)/4 = (n-3)/4+1 by omega] at hfn
    rw [show (n-1)/2 = 1+2*((n-3)/4) by omega] at hfn
    rw [Nat.digits_add] at hfn; repeat rw [List.count_cons] at hfn
    simp [← Nat.digits_of_two_le_of_pos] at hfn
    by_cases h : (n - 3) / 4 ≤ 0
    · replace h : (n - 3) / 4 = 0 := by omega
      simp [h] at hfn
    specialize aux ((n-3)/4) (by omega)
    rw [hf, hf] at aux; zify at hfn
    all_goals omega
-- Finally, we show that if $n%4=1$, $n+1$ has exactly one more $1$ in the base-2 representation
  intro mod4; rw [hf, hf, Nat.digits_of_two_le_of_pos]
  nth_rw 2 [Nat.digits_of_two_le_of_pos]
  simp [show n%2 = 1 by omega, show (n+1)%2 = 0 by omega]
  by_cases h : n = 1; simp [h]
  rw [show n/2 = 0+2*((n-1)/4) by omega]
  rw [show (n+1)/2 = 1+2*((n-1)/4) by omega]
  repeat rw [Nat.digits_add, List.count_cons]
  simp [← Nat.digits_of_two_le_of_pos]
  all_goals omega