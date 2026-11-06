import Mathlib

/- 18. (BUL 1) Find the highest degree $k$ of 1991 for which $1991^{k}$ divides the number  $$ 1990^{1991^{1992}}+1992^{1991^{1990}} $$ -/
theorem other_24354 : IsGreatest {k | 1991 ^ k ∣ 1990 ^ 1991 ^ 1992 + 1992 ^ 1991 ^ 1990} 1991 := by
  -- Lemma: For integer n ≥ 0 and odd intgeer a ≥ 3, a ^ (n + 1) is the largest power of a dividing (a + 1) ^ a ^ n - 1 and also (a - 1) ^ a ^ n + 1.
  have lm (a n : ℕ) (ha₁ : a ≥ 3) (ha₂ : Odd a) : IsGreatest {k | a ^ k ∣ (a + 1) ^ a ^ n - 1} (n + 1) ∧ IsGreatest {k | a ^ k ∣ (a - 1) ^ a ^ n + 1} (n + 1) := by
    -- Perform induction on n.
    induction n with
    | zero =>
      simp [IsGreatest, upperBounds]
      refine ⟨?_, ?_, ?_⟩
      . intro n
        nth_rewrite 2 [show a = a ^ 1 by norm_num]
        rw [Nat.pow_dvd_pow_iff_le_right]
        tauto
        omega
      . rw [Nat.sub_add_cancel (by omega)]
      . intro n
        rw [Nat.sub_add_cancel (by omega)]
        nth_rewrite 2 [show a = a ^ 1 by norm_num]
        rw [Nat.pow_dvd_pow_iff_le_right]
        tauto
        omega
    | succ n hn =>
      simp [IsGreatest, upperBounds] at hn ⊢
      rw [dvd_iff_exists_eq_mul_left, dvd_iff_exists_eq_mul_left] at hn
      obtain ⟨hn₁, hn₂⟩ := hn
      -- Separate the goal into two parts.
      refine ⟨?_, ?_⟩
      . -- Write (a + 1) ^ a ^ n = 1 + N * a ^ (n + 1).
        obtain ⟨⟨N, h₀⟩, h₁⟩ := hn₁
        clear hn₂
        replace h₁ : ¬a ∣ N := by
          by_contra! h₂
          specialize @h₁ (n + 1 + 1)
          rw [h₀] at h₁
          contrapose! h₁
          refine ⟨?_, ?_⟩
          . rw [Nat.pow_add, Nat.mul_comm, Nat.mul_dvd_mul_iff_right (by positivity)]
            simp
            exact h₂
          . simp
        apply Nat.eq_add_of_sub_eq (by apply Nat.one_le_pow') at h₀
        have h₂ : ∃ M : ℕ, (a + 1) ^ a ^ (n + 1) = 1 + N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) := by
          rw [Nat.pow_add, Nat.pow_mul, h₀, show a ^ 1 = a by simp, add_pow]
          use ∑ m ∈ Finset.Ico 3 (a + 1), N ^ m * (a ^ (n + 1)) ^ (m - 3) * Nat.choose a m
          calc
            ∑ m ∈ Finset.range (a + 1), (N * a ^ (n + 1)) ^ m * 1 ^ (a - m) * Nat.choose a m = ∑ m ∈ {0} ∪ {1} ∪ {2}, (N * a ^ (n + 1)) ^ m * 1 ^ (a - m) * Nat.choose a m + ∑ m ∈ Finset.Ico 3 (a + 1), (N * a ^ (n + 1)) ^ m * 1 ^ (a - m) * Nat.choose a m := by
              rw [show {0} ∪ {1} ∪ {2} = Finset.Ico 0 3 by congr, Finset.sum_Ico_consecutive]
              congr
              simp
              norm_num
              omega
            _ = 1 + N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + (∑ m ∈ Finset.Ico 3 (a + 1), N ^ m * (a ^ (n + 1)) ^ (m - 3) * Nat.choose a m) * a ^ (3 * n + 3) := by
              rw [Finset.sum_union, Finset.sum_union]
              simp
              congrm ?_ + ?_ + ?_ + ?_
              . rfl
              . rw [Nat.mul_assoc, <-Nat.pow_add_one]
              . rw [show 2 * n + 2 = (n + 1) * 2 by ring_nf, Nat.pow_mul, Nat.mul_pow]
                ac_rfl
              . rw [Finset.sum_mul, Finset.sum_congr]
                . rfl
                . intro m hm
                  simp at hm
                  rw [show 3 * n + 3 = (n + 1) * 3 by ring_nf, Nat.pow_mul, Nat.mul_pow]
                  nth_rewrite 2 [show m = m - 3 + 3 by rw [Nat.sub_add_cancel hm.1]]
                  rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
                  congrm ?_ * ?_
                  . rfl
                  . rw [Nat.mul_comm, Nat.mul_assoc, Nat.mul_comm, Nat.mul_assoc]
                    nth_rewrite 3 [Nat.mul_comm]
                    rw [Nat.mul_assoc]
                    nth_rewrite 4 [Nat.mul_comm]
                    rfl
              simp
              simp
        obtain ⟨M, h₂⟩ := h₂
        replace h₂ : (a + 1) ^ a ^ (n + 1) - 1 = N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) := by
          rw [h₂, Nat.add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_sub_cancel]
          ac_rfl
        refine ⟨?_, ?_⟩
        . calc
            a ^ (n + 1 + 1) ∣ (N + Nat.choose a 2 * N ^ 2 * a ^ n + M * a ^ (2 * n + 1)) * a ^ (n + 1 + 1) := by apply Nat.dvd_mul_left
            _ = (a + 1) ^ a ^ (n + 1) - 1 := by rw [h₂]; ring_nf
        . intro m hm
          rw [h₂] at hm
          contrapose! hm
          apply Nat.add_one_le_of_lt at hm
          -- It suffices to show that a ^ (n + 3) does not divide the R.H.S.
          suffices h₄ : ¬a ^ (n + 3) ∣ N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) by
            contrapose! h₄
            calc
              a ^ (n + 3) ∣ a ^ m := by apply Nat.pow_dvd_pow; omega
              _ ∣ N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) := h₄
          -- It suffices to show that a ^ (n + 3) divides Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3).
          suffices h₄ : a ^ (n + 3) ∣ Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) by
            by_contra! h₅
            have h₆ : N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) - (Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3)) = N * a ^ (n + 2) := by
              rw [Nat.add_assoc, Nat.add_sub_cancel]
            replace h₆ : a ^ (n + 3) ∣ N * a ^ (n + 2) := by
              rw [<-h₆]
              apply Nat.dvd_sub
              omega
              exact h₅
              exact h₄
            rw [show n + 3 = 1 + (n + 2) by omega, Nat.pow_add] at h₆
            rw [Nat.mul_dvd_mul_iff_right (by positivity)] at h₆
            simp at h₆
            exact h₁ h₆
          apply Nat.dvd_add
          . rw [Nat.choose_two_right]
            have h₃ : Even (a - 1) := by
              apply Nat.Odd.sub_odd ha₂
              simp [Odd]
            simp [Even] at h₃
            obtain ⟨a', h₃⟩ := h₃
            rw [<-Nat.mul_two] at h₃
            rw [h₃, Nat.mul_div_assoc, Nat.mul_div_cancel]
            ring_nf
            rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_dvd_mul_iff_left (by positivity), Nat.mul_two, Nat.pow_add, Nat.mul_assoc]
            apply Nat.dvd_mul_right
            norm_num
            apply Nat.dvd_mul_left
          . rw [show 3 * n + 3 = 2 * n + (n + 3) by omega]
            nth_rewrite 2 [Nat.pow_add]
            rw [<-Nat.mul_assoc]
            apply Nat.dvd_mul_left
      . -- Write (a - 1) ^ a ^ n + (-1) ^ a = N * a ^ (n + 1).
        obtain ⟨⟨N, h₀⟩, h₁⟩ := hn₂
        clear hn₁
        replace h₁ : ¬a ∣ N := by
          by_contra! h₂
          specialize @h₁ (n + 1 + 1)
          rw [h₀] at h₁
          contrapose! h₁
          refine ⟨?_, ?_⟩
          . rw [Nat.pow_add, Nat.mul_comm, Nat.mul_dvd_mul_iff_right (by positivity)]
            simp
            exact h₂
          . simp
        zify at h₀
        symm at h₀
        apply sub_eq_of_eq_add at h₀
        have h₂ : ∃ M : ℤ, (a - 1 : ℕ) ^ a ^ (n + 1) = (-1 : ℤ) ^ a * (1 - N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3)) := by
          rw [Nat.pow_add, pow_mul, <-h₀, show a ^ 1 = a by simp, sub_eq_add_neg, add_pow]
          use ∑ m ∈ Finset.Ico 3 (a + 1), (-1 : ℤ) ^ m * N ^ m * (a ^ (n + 1)) ^ (m - 3) * Nat.choose a m
          calc
            ∑ m ∈ Finset.range (a + 1), (N * a ^ (n + 1)) ^ m * (-1 : ℤ) ^ (a - m) * Nat.choose a m = ∑ m ∈ {0} ∪ {1} ∪ {2}, (N * a ^ (n + 1)) ^ m * (-1 : ℤ) ^ (a - m) * Nat.choose a m + ∑ m ∈ Finset.Ico 3 (a + 1), (N * a ^ (n + 1)) ^ m * (-1 : ℤ) ^ (a - m) * Nat.choose a m := by
              rw [show {0} ∪ {1} ∪ {2} = Finset.Ico 0 3 by congr, Finset.sum_Ico_consecutive]
              congr
              simp
              norm_num
              omega
            _ = (-1 : ℤ) ^ a * (1 - N * a ^ (n + 2) + Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + (∑ m ∈ Finset.Ico 3 (a + 1), (-1 : ℤ) ^ m * N ^ m * (a ^ (n + 1)) ^ (m - 3) * Nat.choose a m) * a ^ (3 * n + 3)) := by
              rw [Finset.sum_union, Finset.sum_union]
              simp
              conv =>
                rhs
                rw [sub_eq_add_neg, mul_add, mul_add, mul_add]
              rw [show (-1) ^ a = -1 by rw [Odd.neg_one_pow ha₂], neg_mul, one_mul]
              congrm ?_ + ?_ + ?_ + ?_
              . simp
              . rw [show (-1) ^ (a - 1) = 1 by rw [Even.neg_one_pow (by apply Nat.Odd.sub_odd ha₂ (by norm_num))]]
                ring
              . rw [show (-1) ^ (a - 2) = -1 by rw [Odd.neg_one_pow (by apply Nat.Odd.sub_even (by linarith only [ha₁]) ha₂ (by norm_num))]]
                ring
              . rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_congr]
                . rfl
                . intro m hm
                  simp at hm
                  ring_nf
                  rw [<-neg_mul, <-neg_mul, mul_assoc, mul_comm (Nat.choose a m : ℤ) ((-1 : ℤ) ^ (a - m)), <-mul_assoc]
                  nth_rewrite 4 [mul_assoc]
                  rw [mul_comm (Nat.choose a m : ℤ) ((-1 : ℤ) ^ m), <-mul_assoc]
                  congrm ?_ * ?_
                  . rw [show (-1) ^ (a - m) = (-1) ^ (a + m) by rw [show a + m = (a - m) + 2 * m by rw [Nat.two_mul, <-Nat.sub_add_comm, <-Nat.add_assoc, Nat.add_sub_cancel]; omega, pow_add, @Even.neg_one_pow _ _ _ (2 * m), mul_one]; apply even_two_mul]
                    ring_nf
                    rw [show (-1) ^ a = -1 by rw [Odd.neg_one_pow ha₂], mul_neg]
                    simp
                    norm_cast
                    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, <-Nat.pow_add, <-Nat.pow_add, <-Nat.pow_add, <-Nat.pow_add]
                    congrm ?_ * ?_ ^ ?_
                    . rfl
                    . rfl
                    . nth_rewrite 3 [Nat.mul_comm]
                      rw [<-Nat.mul_add_one, <-Nat.add_assoc, show 3 + n * 3 = 3 * (n + 1) by omega, <-Nat.add_mul]
                      nth_rewrite 2 [Nat.add_comm]
                      rw [Nat.sub_add_cancel (by apply hm.1)]
                      rw [Nat.mul_add_one]
                      ac_rfl
                  rfl
              simp
              simp
        obtain ⟨M, h₂⟩ := h₂
        rw [show (-1) ^ a = -1 by rw [Odd.neg_one_pow ha₂], neg_mul, one_mul] at h₂
        refine ⟨?_, ?_⟩
        . zify
          calc
            (a ^ (n + 1 + 1) : ℤ) ∣ (N - Nat.choose a 2 * N ^ 2 * a ^ n - M * a ^ (2 * n + 1)) * a ^ (n + 1 + 1) := by apply dvd_mul_left
            _ = (a - 1 : ℕ) ^ a ^ (n + 1) + 1 := by rw [h₂]; ring_nf
        . intro m hm
          zify at hm
          rw [h₂, add_comm, <-sub_eq_add_neg, <-sub_sub, <-sub_sub, <-sub_add] at hm
          simp at hm
          contrapose! hm
          apply Nat.add_one_le_of_lt at hm
          -- It suffices to show that a ^ (n + 3) does not divide the R.H.S.
          suffices h₄ : ¬(a ^ (n + 3) : ℤ) ∣ N * a ^ (n + 2) - Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) - M * a ^ (3 * n + 3) by
            contrapose! h₄
            calc
              (a ^ (n + 3) : ℤ) ∣ a ^ m := by apply pow_dvd_pow; omega
              _ ∣ N * a ^ (n + 2) - Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) - M * a ^ (3 * n + 3) := h₄
          -- It suffices to show that a ^ (n + 3) divides Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3).
          suffices h₄ : (a ^ (n + 3) : ℤ) ∣ Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3) by
            by_contra! h₅
            have h₆ : N * a ^ (n + 2) - Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) - M * a ^ (3 * n + 3) + (Nat.choose a 2 * N ^ 2 * a ^ (2 * n + 2) + M * a ^ (3 * n + 3)) = N * a ^ (n + 2) := by
              simp
            replace h₆ : a ^ (n + 3) ∣ N * a ^ (n + 2) := by
              zify
              rw [<-h₆]
              apply Int.dvd_add
              exact h₅
              exact h₄
            rw [show n + 3 = 1 + (n + 2) by omega, Nat.pow_add] at h₆
            rw [Nat.mul_dvd_mul_iff_right (by positivity)] at h₆
            simp at h₆
            exact h₁ h₆
          apply dvd_add
          . rw [Nat.choose_two_right]
            have h₃ : Even (a - 1) := by
              apply Nat.Odd.sub_odd ha₂
              simp [Odd]
            simp [Even] at h₃
            obtain ⟨a', h₃⟩ := h₃
            rw [<-Nat.mul_two] at h₃
            rw [h₃, Nat.mul_div_assoc, Nat.mul_div_cancel]
            calc
              (a ^ (n + 3) : ℤ) ∣ (a' * N ^ 2 * a ^ n) * a ^ (n + 3) := by apply dvd_mul_left
              _ = (a * a') * N ^ 2 * a ^ (2 * n + 2) := by ring_nf
            norm_num
            apply Nat.dvd_mul_left
          . rw [show 3 * n + 3 = 2 * n + (n + 3) by omega]
            nth_rewrite 2 [pow_add]
            rw [<-mul_assoc]
            apply dvd_mul_left
  -- Small technical lemma to avoid doing direct calculation on 1990 ^ 1991 ^ 1992 + 1992 ^ 1991 ^ 1990.
  have g (a b c : ℕ) (g₀ : 0 < c) : a ^ b ^ c + c ^ b ^ a = (c ^ b ^ a - 1) + (a ^ b ^ c + 1) := by
    rw [<-Nat.sub_add_comm, Nat.add_sub_assoc, Nat.add_sub_cancel, Nat.add_comm]
    simp
    apply Nat.one_le_pow
    exact g₀
  -- Simplify the goal into two parts.
  refine ⟨?_, ?_⟩
  . simp only [Set.mem_setOf]
    rw [g _ _ _ (by norm_num)]
    apply Nat.dvd_add
    . specialize lm 1991 1990
      simp only [true_implies, show 3 ≤ 1991 by norm_num, show Odd 1991 by simp [Odd]; use 995; norm_num] at lm -- We must use "simp only", or otherwise it attempts to deal with 1992 ^ 1991 ^ 1990.
      obtain ⟨lm, _⟩ := lm
      simp only [IsGreatest, Set.mem_setOf] at lm
      obtain ⟨lm, _⟩ := lm
      rw [show 1990 + 1 = 1991 by norm_num, show 1991 + 1 = 1992 by norm_num] at lm
      exact lm
    . specialize lm 1991 1992
      simp only [true_implies, show 3 ≤ 1991 by norm_num, show Odd 1991 by simp [Odd]; use 995; norm_num] at lm -- We must use "simp only", or otherwise it attempts to deal with 1990 ^ 1991 ^ 1992.
      obtain ⟨_, lm⟩ := lm
      simp only [IsGreatest, Set.mem_setOf] at lm
      obtain ⟨lm, _⟩ := lm
      rw [show 1992 + 1 = 1993 by norm_num, show 1991 - 1 = 1990 by norm_num] at lm
      calc
        1991 ^ 1991 ∣ 1991 ^ 1993 := by rw [Nat.pow_dvd_pow_iff_le_right]; norm_num; norm_num
        _ ∣ 1990 ^ 1991 ^ 1992 + 1 := lm
  . simp only [upperBounds, Set.mem_setOf]
    intro n h₀
    by_contra! h₁
    have h₂ : 1991 ^ 1993 ∣ 1990 ^ 1991 ^ 1992 + 1 := by
      specialize lm 1991 1992
      simp only [true_implies, show 3 ≤ 1991 by norm_num, show Odd 1991 by simp [Odd]; use 995; norm_num] at lm -- We must use "simp only", or otherwise it attempts to deal with 1990 ^ 1991 ^ 1992.
      obtain ⟨_, lm⟩ := lm
      simp only [IsGreatest, Set.mem_setOf] at lm
      obtain ⟨lm, _⟩ := lm
      rw [show 1992 + 1 = 1993 by norm_num, show 1991 - 1 = 1990 by norm_num] at lm
      exact lm
    apply Nat.add_one_le_of_lt at h₁
    rw [g _ _ _ (by norm_num)] at h₀
    have h₃ : 1991 ^ 1992 ∣ 1992 ^ 1991 ^ 1990 - 1 := by
      calc
        1991 ^ 1992 ∣ (1992 ^ 1991 ^ 1990 - 1) + (1990 ^ 1991 ^ 1992 + 1) - (1990 ^ 1991 ^ 1992 + 1) := by
          apply Nat.dvd_sub
          apply Nat.le_add_left
          calc
            1991 ^ 1992 ∣ 1991 ^ n := by rw [Nat.pow_dvd_pow_iff_le_right]; linarith only [h₁]; norm_num
            _ ∣ (1992 ^ 1991 ^ 1990 - 1) + (1990 ^ 1991 ^ 1992 + 1) := h₀
          calc
            1991 ^ 1992 ∣ 1991 ^ 1993 := by rw [Nat.pow_dvd_pow_iff_le_right]; norm_num; norm_num
            _ ∣ 1990 ^ 1991 ^ 1992 + 1 := h₂
        _ = 1992 ^ 1991 ^ 1990 - 1 := by rw [Nat.add_sub_cancel]
    specialize lm 1991 1990
    simp only [true_implies, show 3 ≤ 1991 by norm_num, show Odd 1991 by simp [Odd]; use 995; norm_num] at lm -- We must use "simp only", or otherwise it attempts to deal with 1992 ^ 1991 ^ 1990.
    obtain ⟨lm, _⟩ := lm
    simp only [IsGreatest, upperBounds, Set.mem_setOf] at lm
    obtain ⟨_, lm⟩ := lm
    specialize @lm 1992
    rw [show 1991 + 1 = 1992 by norm_num] at lm
    simp only [true_implies, h₃] at lm
    linarith only [lm]
