import Mathlib

open Nat Finset List

/-- The 2-digit integers from 19 to 92 are written consecutively to form the integer
$N=192021\cdots9192$. Suppose that $3^k$ is the highest power of 3 that is a factor of $N$. What is
$k$?

$\text{(A) } 0\quad \text{(B) } 1\quad \text{(C) } 2\quad \text{(D) }
3\quad \text{(E) more than } 3$ -/
theorem number_theory_97342 {N : ℕ}
    (hN : N = (ofDigits 10 $ (List.Ico 1 45) |>.reverse |>.map (fun n ↦ digits 10 n) |>.foldr List.append [])) :
    N % 45 = 9 := by

  -- We want to show that $N$ is congruent to $9$ modulo $45$.
  -- By the Chinese Remainder Theorem, it is enough to show that $N$ is congruent to $9$ modulo $9$
  -- and $N$ is congruent to $0$ modulo $5$.
  suffices N % 5 = 4 ∧ N % 9 = 0 by omega

  split_ands
  -- First, let's show that $N$ is congruent to $4$ modulo $5$. To that end, it is enough to show
  -- $N$ is congruent to $4$ modulo $10$ because $5$ divides $10$.
  · suffices N % 10 = 4 by omega

    -- We know that the remainder of a number modulo $10$ is equal to the last digit of the number.
    convert Nat.ofDigits_mod_eq_head! 10 (digits 10 N)
    · exact Eq.symm (ofDigits_digits 10 N)
    -- Which is 4 by inspection
    · rw [hN]
      decide +native

  -- Now, let's show that $N$ is congruent to $0$ modulo $9$.

  -- Let's find the remainder of $N$ modulo $9$. We know that the remainder of a number modulo $9$ is equal to remainder of the sum of its digits.
  have mod_nine_eq_sum_digts_mod_nine (n : ℕ) : n % 9 = (digits 10 n).sum % 9 := by
    show n ≡ (digits 10 n).sum [MOD 9]
    exact modEq_nine_digits_sum n

  -- Now, let's show that the digits of $N$ are the concatenation of the digits of the numbers from
  -- 1 to 44.

  -- To that end, we need a technical lemma. If $L$ is a list of lists, then, an element of the
  -- concatenation of the lists in $L$ is an element of one of the lists in $L$.
  have mem_foldr_append_iff {α : Type} (L : List (List α)) (d : α) :
      d ∈ foldr List.append [] L ↔ ∃ l ∈ L, d ∈ l := by
    induction' L with l L' ih
    · simp
    · constructor
      · intro h
        simp at h ⊢
        rcases h with (h | h)
        · left; exact h
        · right; exact ih.mp h
      · intro h
        simp at h ⊢
        rcases h with (h | ⟨l', hl', hd⟩)
        · left; exact h
        · right; exact ih.mpr ⟨l', hl', hd⟩

  -- Now, using the technical lemma we just proved, we can show that the digits of $N$ are
  -- the concatenation of the digits of the numbers from 1 to 44.
  have hNd : digits 10 N = (List.Ico 1 45 |>.reverse |>.map (digits 10) |>.foldr List.append []) := by
    rw [hN, digits_ofDigits 10 (by norm_num)]
    · intro d hd
      rw [mem_foldr_append_iff] at hd
      rcases hd with ⟨l, hl, hdl⟩
      simp at hl
      rcases hl with ⟨n, hn, hnl⟩
      rw [←hnl] at hdl
      exact digits_lt_base' hdl
    · decide +kernel

  -- Therefore, the sum of the digits of $N$ is equal to the sum of the digits of the numbers from
  -- 1 to 44.
  have : (digits 10 N).sum = (List.Ico 1 45 |>.map (fun n ↦ digits 10 n) |>.map List.sum |>.sum) := by
    have sum_foldr_append (L : List (List ℕ)) :
        (foldr List.append [] L).sum = (L.map (fun l ↦ l.sum)).sum := by
      induction' L with l L' ih
      · simp
      · simp [ih]
    rw [hNd, sum_foldr_append, List.map_reverse, List.map_reverse, List.sum_reverse]

  -- Before, calculating the sum of the digits of $N$ modulo $9$, we list some formulas we will use.

  -- The sum of the integers from 0 to $n-1$ is equal to $n(n-1)/2$.
  have sum_range (n : ℕ) : (List.range n).sum = n * (n - 1) / 2 := by
    induction' n with n ih
    · simp
    · rw [List.range_succ, List.sum_append, List.sum_singleton, ih]
      by_cases hn : n = 0
      · subst hn; rfl

      let m := n - 1
      have : n = m + 1 := by omega
      clear_value m
      subst this
      simp

      calc _ = (m + 1) * m / 2 + ((m + 1) * 2 / 2) := by omega
           _ = ((m + 1) * m + (m + 1) * 2) / 2 := by omega
           _ = ((m + 1) * (m + 2)) / 2 := by rw [mul_add]
           _ = _ := by congr 1; ring

  -- Then, using this fact, we have: $a + (a + 1) + \dots b - 1 =
  -- (0 + 1 + \dots b - 1) - (0 + 1 + \dots + a - 1) = \frac{b (b - 1)}{2} + \frac{a (a - 1)}{2}$
  have sum_Ico {a b : ℕ} (h : a ≤ b) : (List.Ico a b).sum = (b * (b - 1)) / 2 - (a * (a - 1)) / 2 := by
    calc _ = (List.Ico 0 a).sum + (List.Ico a b).sum - (List.Ico 0 a).sum := by omega
         _ = (List.Ico 0 a ++ List.Ico a b).sum - (List.Ico 0 a).sum := by rw [List.sum_append]
         _ = (List.Ico 0 b).sum - (List.Ico 0 a).sum := by rw [List.Ico.append_consecutive (by omega) h]
         _ = (List.range b).sum - (List.range a).sum := by rw [List.Ico.zero_bot, List.Ico.zero_bot]
         _ = (b * (b - 1)) / 2 - (a * (a - 1)) / 2 := by rw [sum_range, sum_range]

  -- Now, let's proceed to calculate the sum of the digits of $N$ modulo $9$.
  -- We know that $N$ is congruent to its sum of digits modulo $9$.
  calc _ = (digits 10 N).sum % 9 := by apply mod_nine_eq_sum_digts_mod_nine
  -- Sum of the digits of $N$ is equal to the sum of the digits of the numbers from 1 to 44.
        _ = (List.Ico 1 45 |>.map (fun n ↦ digits 10 n) |>.map List.sum |>.sum) % 9 := by rw [this]
        _ = (List.Ico 1 45 |>.map (fun n ↦ digits 10 n) |>.map List.sum |>.map (fun x ↦ x % 9) |>.sum) % 9 := by rw [List.sum_nat_mod]
  -- Moreover, the sum of digits of a number in the interval $[1, 45)$ is also congruent to itself
  -- modulo $9$. Therefore, $N$ is congruent to the sum of the numbers from 1 to 44 modulo $9$.
        _ = (List.Ico 1 45 |>.map  (fun x ↦ x % 9) |>.sum) % 9 := by congr 2; rw [List.map_map, List.map_map]; congr; funext n; symm; apply mod_nine_eq_sum_digts_mod_nine
        _ = (List.Ico 1 45 |>.sum) % 9 := by rw [←List.sum_nat_mod]
  -- Using our summation formulas, the sum of the numbers from 1 to 44 is equal to 990.
        _ = 990 % 9 := by rw [sum_Ico (by norm_num)]
  -- 990 is congruent to 3 modulo $9$.
        _ = _ := by rfl