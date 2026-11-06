import Mathlib
set_option maxHeartbeats 300000

-- A lemma for getting the leftmost digit of a number in decimal representation.
lemma get_leftmost (n : ℕ) (hn : n ≠ 0) :
    n / 10 ^ (Nat.log 10 n) = (Nat.digits 10 n).getLast! := by
  -- The leftmost digit can be attained with index (Nat.log 10 n), which is one less than the total number of digits.
  have : (Nat.digits 10 n).getLast! = (Nat.digits 10 n)[Nat.log 10 n]! := by
    rw [List.getLast!_eq_getElem!, Nat.digits_len _ _ (by norm_num) hn, Nat.add_sub_cancel]
  rw [this]
  clear this
  replace hn : n ∈ Finset.Ico (10 ^ Nat.log 10 n) (10 ^ (Nat.log 10 n + 1)) := by
    simp
    rw [<-Nat.log_eq_iff]
    simp [hn]
  revert hn
  -- Generalize k = Nat.log 10 n to perform induction on k.
  obtain k := Nat.log 10 n
  revert n
  simp
  induction' k with k hk
  <;> intro n _ _
  . -- Base case k = 0.
    have h₀ := Nat.digits_len 10 n (by norm_num) (by omega)
    rw [Nat.log_eq_zero_iff.mpr (by omega)] at h₀
    obtain ⟨m, h₀⟩ := List.length_eq_one.mp h₀
    have h₁ := (Nat.ofDigits_digits 10 n).symm
    simp [h₀] at h₁ ⊢
    assumption
  . -- Inductive case.
    have := @Nat.digits_eq_cons_digits_div 10 n (by norm_num) (by omega)
    simp [this]
    rw [Nat.pow_succ', <-Nat.div_div_eq_div_mul]
    apply hk
    <;> omega

/- Man beweise, dass es keine positive ganze Zahl $n$ mit der folgenden Eigenschaft gibt: Für $k=1,2, \ldots, 9$ ist die - in dezimaler Schreibweise - linke Ziffer von $(n+k)$ ! gleich $k$. -/
theorem number_theory_606021 :
    ¬∃ n : ℕ, 0 < n ∧ ∀ k ∈ Finset.Icc 1 9, (Nat.digits 10 (Nat.factorial (n + k))).getLast! = k := by
  -- Assume such integer n exists.
  push_neg
  intro n hn
  by_contra! h
  by_cases h₀ : ∃ k ∈ Finset.Icc 2 9, ∃ j : ℕ, n + k = 10 ^ j
  . -- Suppose there is some k ∈ [2, 9] such that n + k = 10 ^ j for some j, then we have two terms with same leading digit.
    obtain ⟨k, hk, j, h₀⟩ := h₀
    simp at hk
    have h₁ := h (k - 1) (by simp; omega)
    have h₂ := h k (by simp; omega)
    -- We have (n + k)! = (n + k - 1)! * (n + k).
    have h₃ := Nat.factorial_succ (n + k - 1)
    rw [Nat.sub_add_cancel (by omega)] at h₃
    nth_rw 2 [h₀] at h₃
    rw [h₃, Nat.digits_base_pow_mul (by norm_num) (by apply Nat.factorial_pos), List.getLast!_eq_getLast?_getD, List.getLast?_append, Option.or_of_isSome] at h₂
    rw [List.getLast!_eq_getLast?_getD, <-Nat.add_sub_assoc (by omega)] at h₁
    -- A contradiction k - 1 = k is derived.
    omega
    -- Verify that (n + k - 1)! ≠ 0.
    simp [Nat.digits_eq_nil_iff_eq_zero]
    exact (n + k - 1).factorial_pos.ne'
  . -- Otherwise, there exists integer j such that 10 ^ j < n + 2 < ⋯ < n + 9 < 10 ^ (j + 1).
    have h₁ : ∃ j : ℕ, 10 ^ j < n + 2 ∧ n + 9 < 10 ^ (j + 1) := by
      -- Let j be the largest exponent k such that 10 ^ k ≤ n + 1
      set j := Nat.log 10 (n + 1) with hj
      use j
      rw [hj]
      -- We have 10 ^ j ≤ n + 1 < 10 ^ (j + 1).
      rw [Nat.log_eq_iff (by simp)] at hj
      refine ⟨?_, ?_⟩
      . omega
      . -- Assume on the contrary that 10 ^ (j + 1) ≤ n + 9, then it contradicts with the assumption h₀.
        by_contra! h
        absurd h₀
        use 10 ^ (Nat.log 10 (n + 1) + 1) - n
        refine ⟨?_, ?_⟩
        . simp
          refine ⟨by omega, by omega⟩
        . use Nat.log 10 (n + 1) + 1
          rw [Nat.add_sub_cancel']
          omega
    obtain ⟨j, h₁⟩ := h₁
    have g : ∀ k ∈ Finset.Icc 1 9, ∃ m : ℕ, m = Nat.log 10 (n + k).factorial ∧ k * 10 ^ m ≤ Nat.factorial (n + k) ∧ Nat.factorial (n + k) < (k + 1) * 10 ^ m := by
      intro k hk
      specialize h k hk
      -- Apply the lemma get_leftmost to get the leftmost digit of (n + k)!.
      have h₂ := get_leftmost (n + k).factorial ((n + k).factorial_pos.ne')
      rw [h] at h₂
      use Nat.log 10 (n + k).factorial
      -- This is simply the definition of natural number division.
      rw [Nat.eq_iff_le_and_ge, and_comm, Nat.le_div_iff_mul_le (by positivity), Nat.div_le_iff_le_mul_add_pred (by positivity)] at h₂
      refine ⟨by rfl, h₂.1, ?_⟩
      replace h₂ := h₂.2
      rw [<-Nat.add_sub_assoc (by rw [Nat.one_le_iff_ne_zero]; positivity), <-Nat.mul_succ, <-Nat.lt_add_one_iff, Nat.sub_add_cancel (by rw [Nat.one_le_iff_ne_zero]; positivity), mul_comm] at h₂
      exact h₂
    -- Since the leading digit of (n + 9)! is 9, we can find integer a such that 9 * 10 ^ a < (n + 9)! < 10 ^ (a + 1).
    obtain ⟨a, g₉₀, g₉₁, g₉₂⟩ := g 9 (by simp)
    -- Similarly, we can find integer b such that 8 * 10 ^ b < (n + 8)! < 9 * 10 ^ b.
    obtain ⟨b, g₈₀, g₈₁, g₈₂⟩ := g 8 (by simp)
    -- Clearly we have b ≤ a.
    have h₄ : b ≤ a := by
      rw [g₈₀, g₉₀]
      apply Nat.log_mono_right
      apply Nat.factorial_le
      omega
    -- Combining the two results above, we have 10 ^ (a - b) ≤ n + 9 ≤ (5 / 4) * 10 ^ (a - b).
    have h₅ : (10 : ℚ) ^ (a - b : ℤ) ≤ n + 9 ∧ n + 9 ≤ (5 / 4 : ℚ) * (10 : ℚ) ^ (a - b : ℤ) := by
      refine ⟨?_, ?_⟩
      . -- Show that 10 ^ (a - b) ≤ n + 9 by combining the inequalities above.
        calc
          _ = ((9 * 10 ^ a) / (9 * 10 ^ b) : ℚ) := by
            simp [zpow_sub₀, mul_div_mul_left]
          _ ≤ (n + 9).factorial / (n + 8).factorial := by
            apply div_le_div₀
            . positivity
            . norm_cast
            . positivity
            . simp at g₈₂
              apply le_of_lt at g₈₂
              norm_cast
          _ = n + 9 := by
            field_simp
            norm_cast
      . -- Show that (n + 9) ≤ (5 / 4) * 10 ^ (a - b) by combining the inequalities above.
        calc
          _ = ((n + 9).factorial / (n + 8).factorial : ℚ) := by
            field_simp
            norm_cast
          _ ≤ ((10 * 10 ^ a) / (8 * 10 ^ b) : ℚ) := by
            apply div_le_div₀
            . positivity
            . simp at g₉₂
              apply le_of_lt at g₉₂
              norm_cast
            . positivity
            . norm_cast
          _ = (5 / 4 : ℚ) * (10 : ℚ) ^ (a - b : ℤ) := by
            field_simp
            rw [<-mul_assoc, mul_comm _ 8, mul_assoc 8, mul_assoc 5, <-zpow_natCast 10 b, <-zpow_add₀ (by norm_num)]
            simp
            ring
    -- We have j = a - b as a consequence.
    have h₆ : j = a - b := by
      apply le_antisymm
      . -- First show that j ≤ a - b.
        have : (10 ^ j : ℚ) < 10 ^ (a - b + 1 : ℤ) := by
          calc
            _ < (n + 2 : ℚ) := by
              norm_cast
              exact h₁.1
            _ ≤ 10 * 10 ^ (a - b : ℤ) := by
              linarith
            _ = 10 ^ (a - b + 1 : ℤ) := by
              rw [zpow_add₀ (by norm_num)]
              ring
        rw [<-zpow_natCast 10 j, zpow_lt_zpow_iff_right₀ (by norm_num)] at this
        norm_cast at this
        omega
      . -- Next show that a - b ≤ j.
        have : 10 ^ (a - b : ℤ) < (10 ^ (j + 1) : ℚ) := by
          calc
            _ ≤ (n + 9 : ℚ) := h₅.1
            _ < 10 ^ (j + 1) := by
              norm_cast
              exact h₁.2
        rw [<-zpow_natCast 10 (j + 1), zpow_lt_zpow_iff_right₀ (by norm_num)] at this
        norm_cast at this
        omega
    zify at h₆
    rw [Int.ofNat_sub] at h₆
    rw [<-h₆] at h₅
    norm_cast at h₅
    -- Since the leading digit of (n + 1)! is 1, we can find integer c such that 10 ^ c < (n + 1)! < 2 * 10 ^ c.
    obtain ⟨c, g₁₀, g₁₁, g₁₂⟩ := g 1 (by simp)
    simp at g₁₁ g₁₂
    -- Similarly, we have integer d such that 4 * 10 ^ d < (n + 4)! < 5 * 10 ^ d.
    obtain ⟨d, g₄₀, g₄₁, g₄₂⟩ := g 4 (by simp)
    -- We show that 10 ^ (3j + c) < (n + 4)! and (n + 4)! < 4 * 10 ^ (3j + c).
    have g₄₃ : 10 ^ (3 * j + c) < (n + 4).factorial := by
      qify
      calc
        _ = (10 ^ c * 10 ^ j * 10 ^ j * 10 ^ j : ℚ) := by
          norm_cast
          rw [<-Nat.pow_add, <-Nat.pow_add, <-Nat.pow_add]
          ring_nf
        _ < (n + 1).factorial * (n + 2) * (n + 3) * (n + 4) := by
          -- We use 10 ^ c < (n + 1)! and 10 ^ j < n + 2 < n + 3 < n + 4.
          norm_cast
          apply Nat.mul_lt_mul_of_le_of_lt _ _ (by positivity)
          iterate 2 apply Nat.mul_le_mul
          . exact g₁₁
          . omega
          . omega
          . omega
        _ = (n + 4).factorial := by
          norm_cast
          rw [mul_comm, mul_assoc, mul_comm (n + 1).factorial, mul_comm (n + 2), mul_assoc, <-Nat.factorial_succ, <-Nat.factorial_succ, <-Nat.factorial_succ]
    have g₄₄ : (n + 4).factorial < 4 * 10 ^ (3 * j + c) := by
      qify
      calc
        _ = ((n + 1).factorial * (n + 2) * (n + 3) * (n + 4) : ℚ) := by
          norm_cast
          rw [mul_comm, mul_assoc, mul_comm (n + 1).factorial, mul_comm (n + 2), mul_assoc, <-Nat.factorial_succ, <-Nat.factorial_succ, <-Nat.factorial_succ]
        _ < 2 * 10 ^ c * (n + 9) * (n + 9) * (n + 9) := by
          norm_cast
          apply Nat.mul_lt_mul_of_le_of_lt _ _ (by positivity)
          iterate 2 apply Nat.mul_le_mul
          . exact le_of_lt g₁₂
          . omega
          . omega
          . omega
        _ ≤ 2 * 10 ^ c * ((5 / 4 : ℚ) * 10 ^ j) ^ 3 := by
          -- We use (n + 1)! ≤ 2 * 10 ^ c and n + 2 < n + 3 < n + 4 < n + 9 < (5 / 4) * 10 ^ j.
          rw [mul_assoc, mul_assoc, <-pow_two, <-pow_succ']
          simp
          apply pow_le_pow_left₀
          . positivity
          . push_cast at h₅
            exact h₅.2
        _ < 4 * 10 ^ (3 * j + c) := by
          ring_nf
          field_simp
          rw [mul_div_assoc]
          apply mul_lt_mul_of_pos_left (by norm_num) (by positivity)
    -- We get d < 3j + c.
    have h₇ : d < 3 * j + c := by
      have := g₄₁.trans_lt g₄₄
      simp at this
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at this
      exact this
    -- We get (n + 4)! < (n + 4)!, which is clearly a contradiction.
    have h₈ : (n + 4).factorial < (n + 4).factorial := by
      calc
        _ < (4 + 1) * 10 ^ d := g₄₂
        _ < 10 * 10 ^ d := by
          simp
        _ ≤ 10 ^ (3 * j + c) := by
          rw [<-pow_succ', Nat.pow_le_pow_iff_right (by norm_num)]
          omega
        _ < (n + 4).factorial := g₄₃
    absurd h₈
    simp
    exact h₄
