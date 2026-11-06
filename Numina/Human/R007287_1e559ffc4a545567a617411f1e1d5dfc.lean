import Mathlib

open Nat

/-- The integer $n$ is the smallest positive multiple of $15$ such that every digit of $n$ is
either $8$ or $0$. Compute $\frac{n}{15}$. -/
theorem number_theory_94603 {n : ℕ}
    (hn : IsLeast {m : ℕ | 0 < m ∧ 15 ∣ m ∧ ∀ d ∈ digits 10 m, d = 8 ∨ d = 0} n) :
    n / 15 = 592 := by

  -- We will show that $n = 8880$.
  suffices n = 8880 from by simp [this]
  apply IsLeast.unique (s := {m : ℕ | 0 < m ∧ 15 ∣ m ∧ ∀ d ∈ digits 10 m, d = 8 ∨ d = 0}) hn

  -- Clearly, $8880$ satisfies the conditions.
  refine ⟨by simp; norm_num, ?_⟩

  -- Let's show that $8880$ is the smallest such number. Let $n$ be a number satisfying the
  -- conditions. We will show that $n \geq 8880$.
  rintro n ⟨hnpos, hndvd, hndig⟩

  -- We will make a lot of little observations about $n$ and prove a lot of helper lemmas.

  -- The first helper lemma is that, if all digits of a number are $0$, then the number is $0$.
  have ofDigits_replicate_0_eq_0 (k b : ℕ) : ofDigits b (List.replicate k 0) = 0 := by
    induction' k with k ih
    · rfl
    · simp [List.replicate_succ, ofDigits_cons, ih]

  have digits_ne_nil : digits 10 n ≠ [] := by rw [digits_ne_nil_iff_ne_zero]; linarith only [hnpos]

  have {l : List ℕ} (hl : ∀ d ∈ l, d = 8 ∨ d = 0) : l.length = l.count 0 + l.count 8 := by
    let l' := l.map (fun d => d == 0)
    convert (l'.count_add_count_not true).symm using 2
    · simp [l']
    · simp [l', List.count]
      rfl
    · simp [l', List.count]
      apply List.countP_congr
      intro d hd
      rcases hl d hd with (rfl | rfl) <;> simp

  -- Only digits in the decimal expansion of $n$ are $0$ and $8$. Therefore, the length of the
  -- decimal expansion of $n$ is equal to the count of $0$s and $8$s in the decimal expansion of
  -- $n$.
  have digits_len_eq_digits_count_0_add_digits_count_8 : (digits 10 n).length =
      (digits 10 n).count 0 + (digits 10 n).count 8 := this hndig

  -- There is at least one $0$ in the decimal expansion of $n$ because otherwise $n$ would be $0$.
  have pos_mem_digits_of_pos {n b : ℕ} (hn : 0 < n) : ∃ d : ℕ, 0 < d ∧ d ∈ digits b n := by
    contrapose! hn; simp

    replace h : ∀ d, d ∈ digits b n → d = 0 := by
      intro d hd
      contrapose! hd
      apply hn d
      omega

    have : digits b n = List.replicate (digits b n).length 0 := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_replicate]
        convert h _ _
        simp only [List.getElem_mem]

    rw [←ofDigits_digits b n, this, ofDigits_replicate_0_eq_0]

  -- The least significant digit of the base-$b$ expansion of an integer $n$ is the remainder of the
  -- division of $n$ by $b$. Moreover, the result of the division of $n$ by $b$ is the integer part
  -- of the division of $n$ by $b$.
  have div_add_digits_head! (n : ℕ) {b : ℕ} (hb : 1 < b) : n = (n/b)*b + (digits b n).head! := by
    by_cases hn : n = 0
    · subst hn; simp
    · nth_rewrite 1 [←div_add_mod' n b]
      congr
      nth_rewrite 1 [←ofDigits_digits b n, ofDigits_mod_eq_head! b (digits b n)]
      apply mod_eq_of_lt
      apply digits_lt_base (m := n) ‹_›
      apply List.head!_mem_self
      rwa [digits_ne_nil_iff_ne_zero]

  -- An integer $n$ is divisible by $5$ if and only if it is equal to $0$ or $5$ mod $10$.
  have five_dvd_iff_eq_0_or_5_mod_10 {n : ℕ} : 5 ∣ n ↔ n % 10 = 0 ∨ n % 10 = 5 := by omega

  -- Therefore, an integer $n$ is divisible by $5$ if and only if the least significant digit of the
  -- decimal expansion of $n$ is $0$ or $5$.
  have five_dvd_iff_digits_head!_eq_0_or_5 (n : ℕ) :
      5 ∣ n ↔ ((digits 10 n).head! = 0 ∨ (digits 10 n).head! = 5) := by
    by_cases n = 0
    · subst_vars; simp
    · rw [five_dvd_iff_eq_0_or_5_mod_10]
      constructor <;> rintro (h | h)
      · left
        suffices (digits 10 n).head! % 10 = 0 from ?_
        · rwa [mod_eq_of_lt] at this
          apply digits_lt_base (m := n) (by norm_num)
          apply List.head!_mem_self
          rwa [digits_ne_nil_iff_ne_zero]
        · rwa [←ofDigits_mod_eq_head! 10 (digits 10 n), ofDigits_digits]
      · right
        suffices (digits 10 n).head! % 10 = 5 from ?_
        · rwa [mod_eq_of_lt] at this
          apply digits_lt_base (m := n) (by norm_num)
          apply List.head!_mem_self
          rwa [digits_ne_nil_iff_ne_zero]
        · rwa [←ofDigits_mod_eq_head! 10 (digits 10 n), ofDigits_digits]
      · left
        rw [div_add_digits_head! (b := 10) n (by norm_num), h]
        omega
      · right
        rw [div_add_digits_head! (b := 10) n (by norm_num), h]
        omega

  have List.head!_eq_head_of_ne_nil {l : List ℕ} (hl : l ≠ []) :
      l.head! = l.head hl := by
    match l with
    | [] => contradiction
    | a :: l => rfl

  -- Our integer $n$ is divisible by $15$ and hence by $5$, so the least significant digit of its
  -- decimal expansion must be $0$.
  have digits_head_eq_0 : (digits 10 n).head digits_ne_nil = 0 := by
    rcases (five_dvd_iff_digits_head!_eq_0_or_5 n).mp (by omega) with (h | h)
    · rw [←h]
      symm
      apply List.head!_eq_head_of_ne_nil (l := (digits 10 n))
    · exfalso
      have : (digits 10 n).head! ∈ digits 10 n := by
        apply List.head!_mem_self
        rw [digits_ne_nil_iff_ne_zero]
        linarith only [hnpos]
      rcases hndig (digits 10 n).head! ‹_› with (h' | h') <;> rw [h] at h' <;> contradiction

  -- This means that the number of $0$s in the decimal expansion of $n$ is at least $1$.
  have one_le_digits_count_0 : 1 ≤ (digits 10 n).count 0 := by
    suffices 0 < (digits 10 n).count 0 from by omega
    rw [List.count_pos_iff, ←digits_head_eq_0]
    apply List.head_mem

  -- If a list of natural numbers contains only $0$ and $8$, then the sum of the elements of the
  -- list is $8$ times the count of $8$s in the list.
  have sum_eq_8_mul_count_8 {l : List ℕ} (hl : ∀ d ∈ l, d = 8 ∨ d = 0) :
      l.sum = 8 * l.count 8 := by
    induction' l with a l ih
    · rfl
    · simp at hl
      rw [List.sum_cons, List.count_cons, ih hl.2]
      rcases hl.1 with (rfl | rfl) <;> dsimp <;> ring

  -- Our number $n$ is divisible by $15$ and hence by $3$, so the sum of the digits of the decimal
  -- expansion of $n$ is divisible by $3$.
  have : 3 ∣ (digits 10 n).sum := by rw [←Nat.three_dvd_iff]; omega

  have : 3 ∣ 8 * (digits 10 n).count 8 := by
    convert this using 1
    rw [sum_eq_8_mul_count_8 hndig]

  -- Then, the count of $8$s in the decimal expansion of $n$ is divisible by $3$.
  have three_dvd_digits_count_8 : 3 ∣ (digits 10 n).count 8 := by omega

  -- Inpartilar, the count of $8$s in the decimal expansion of $n$ is at least $3$ because
  -- if there are no $8$s, then $n = 0$.
  have three_le_digits_count_8 : 3 ≤ (digits 10 n).count 8 := by
    by_cases h : (digits 10 n).count 8 = 0
    · exfalso
      suffices n = 0 from by omega
      rw [←ofDigits_digits 10 n]
      convert ofDigits_replicate_0_eq_0 (digits 10 n).length 10 using 2
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp
        contrapose! h
        replace h : (digits 10 n)[i] = 8 := by
          rcases hndig (digits 10 n)[i] (by simp) with (_ | _)
          · assumption
          · contradiction
        suffices 0 < List.count 8 (digits 10 n) from by omega
        rw [List.count_pos_iff, ←h]
        simp
    · omega

  -- Therefore, the length of the decimal expansion of $n$ is at least $4$.
  have four_le_digits_len : 4 ≤ (digits 10 n).length := by
    rw [digits_len_eq_digits_count_0_add_digits_count_8]
    linarith only [three_le_digits_count_8, one_le_digits_count_0]

  -- Let's do a case analysis on the length of the decimal expansion of $n$.
  by_cases h : (digits 10 n).length > 4

  -- If the length of the decimal expansion of $n$ is greater than $4$, then $n$ is surely greater
  -- than $8880$.
  · have h : 5 ≤ (digits 10 n).length := by omega
    rw [digits_len 10 n (by norm_num) (by linarith only [hnpos])] at h
    replace h : 4 ≤ log 10 n := by linarith
    replace h : 10^4 ≤ n := pow_le_of_le_log (by linarith only [hnpos]) h
    linarith only [h]

  -- Let's focus on the case where the length of the decimal expansion of $n$ is less than or equal
  -- to $4$. Then, the length of the decimal expansion of $n$ is exactly $4$ because we have already
  -- shown that it is at least $4$.
  · replace h : (digits 10 n).length = 4 := by omega

    -- Then, the number of $0$s in the decimal expansion of $n$ is exactly $1$.
    have digits_count_0_eq_1 : (digits 10 n).count 0 = 1 := by
      linarith only [h, three_le_digits_count_8, one_le_digits_count_0,
                      digits_len_eq_digits_count_0_add_digits_count_8]

    -- And, the number of $8$s in the decimal expansion of $n$ is exactly $3$.
    have digits_count_8_eq_3 : (digits 10 n).count 8 = 3 := by
      linarith only [h, three_le_digits_count_8, one_le_digits_count_0,
                      digits_len_eq_digits_count_0_add_digits_count_8]

    -- The single $0$ in the decimal expansion of $n$ is the least significant digit of $n$, so
    -- these conditions forces $n = 8880$.
    have : (digits 10 n).tail.count 8 = 3 := by
      simp [List.count_tail (h := digits_ne_nil), digits_count_8_eq_3, digits_head_eq_0]

    have : (digits 10 n).tail = [8, 8, 8] := by
      suffices (digits 10 n).tail = List.replicate 3 8 from by rw [this]; rfl
      rw [List.eq_replicate_iff]
      refine ⟨by simp [h], ?_⟩
      simp_rw [eq_comm (b := 8), ←List.count_eq_length]
      convert this
      simp [h]

    have : digits 10 n = [0, 8, 8, 8] := by
      calc _ = (digits 10 n).head digits_ne_nil :: (digits 10 n).tail := by simp
            _ = 0 :: [8, 8, 8] := by rw [digits_head_eq_0, this]
            _ = [0, 8, 8, 8] := by rfl

    rw [←ofDigits_digits 10 n, this]
    decide