import Mathlib

/- From the following infinite list of numbers, how many are integers? $$\sqrt{4096},\sqrt[3]{4096},\sqrt[4]{4096},\sqrt[5]{4096},\sqrt[6]{4096},\ldots$$ -/
theorem algebra_10679 : {n : ℕ | n > 1 ∧ ∃ k : ℕ, (4096 : ℝ) ^ ((1 : ℝ) / n) = k}.ncard = 5 := by
  -- Only n = 2, 3, 4, 6, 12 satisfies the property.
  suffices h : {n : ℕ | n > 1 ∧ ∃ k : ℕ, (4096 : ℝ) ^ ((1 : ℝ) / n) = k} = {2, 3, 4, 6, 12} by
    calc
      {n : ℕ | n > 1 ∧ ∃ k : ℕ, (4096 : ℝ) ^ ((1 : ℝ) / n) = k}.ncard = Set.ncard {2, 3, 4, 6, 12} := by rw [h]
      _ = ({2, 3, 4, 6, 12} : Finset ℕ).toSet.ncard := by simp
      _ = Finset.card {2, 3, 4, 6, 12} := Set.ncard_coe_Finset _
      _ = 5 := by simp
  ext n
  apply Iff.intro
  . -- If n satisfies the condition, then n = 2, 3, 4, 6, 12.
    simp [- one_div]
    intro hn x heq
    -- We have 2 ^ 12 = x ^ n.
    replace heq : 2 ^ 12 = x ^ n := by
      rify
      calc
        (2 ^ 12 : ℝ) = (4096 : ℝ) := by norm_num
        _ = (4096 ^ ((1 : ℝ) / n)) ^ (n : ℝ) := by rw [<-Real.rpow_mul]; field_simp; norm_num
        _ = (x : ℝ) ^ (n : ℝ) := by rw [heq]
        _ = (x : ℝ) ^ n := by norm_cast
    -- We have x ≥ 2.
    have hx : x ≥ 2 := by
      by_contra!
      interval_cases x
      . -- x = 0, impossible.
        rw [Nat.zero_pow] at heq
        norm_num at heq
        omega
      . -- x = 1, impossible.
        simp at heq
    -- We have n ≤ 12.
    have hn' : n ≤ 12 := by
      by_contra!
      -- We can derive a wrong equation.
      have weq : 2 ^ 12 < x ^ n := by
        calc
          2 ^ 12 ≤ x ^ 12 := by apply Nat.pow_le_pow_of_le_left; assumption
          _ < x ^ n := by apply Nat.pow_lt_pow_of_lt; omega; assumption
      absurd weq
      linarith only [heq]
    -- If n > 6, then only n = 12 is possible.
    have lm (h : n > 6) : n = 12 := by
      by_contra!
      replace hn' : n < 12 := by
        omega
      -- We have x < 4.
      have hx' : x < 4 := by
        by_contra!
        -- We can derive a wrong equation.
        have weq : 2 ^ 12 < x ^ n := by
          calc
            2 ^ 12 = 4 ^ 6 := by norm_num
            _ ≤ x ^ 6 := by apply Nat.pow_le_pow_of_le_left; assumption
            _ < x ^ n := by apply Nat.pow_lt_pow_of_lt; omega; assumption
        absurd weq
        omega
      interval_cases x
      . -- Case x = 2 but n < 12, impossible.
        have weq : 2 ^ 12 > 2 ^ n := by
          rw [gt_iff_lt]
          apply Nat.pow_lt_pow_of_lt; norm_num; assumption
        absurd weq
        omega
      . -- Case x = 3: impossible.
        have wh : 3 ∣ 2 ^ 12 := by
          calc
            3 = 3 ^ 1 := by norm_num
            _ ∣ 3 ^ n := by apply Nat.pow_dvd_pow; omega
            _ = 2 ^ 12 := by exact heq.symm
        norm_num at wh
    interval_cases n
    . -- Case n = 2, possible.
      tauto
    . -- Case n = 3, possible.
      tauto
    . -- Case n = 4, possible.
      tauto
    . -- Case n = 5, impossible.
      -- We would have 5 ≤ x.
      have wh₀ : 5 ≤ x := by
        by_contra!
        have weq : 2 ^ 12 > x ^ 5 := by
          calc
            2 ^ 12 > 5 ^ 5 := by norm_num
            _ ≥ x ^ 5 := by apply Nat.pow_le_pow_of_le_left; omega
        absurd weq
        omega
      -- We also have x < 6.
      have wh₁ : x < 6 := by
        by_contra!
        have weq : 2 ^ 12 < x ^ 5 := by
          calc
            2 ^ 12 < 6 ^ 5 := by norm_num
            _ ≤ x ^ 5 := by apply Nat.pow_le_pow_of_le_left; omega
        absurd weq
        omega
      interval_cases x
      norm_num at heq
    . -- Case n = 6, possible.
      tauto
    all_goals
      right
      right
      right
      right
      apply lm (by norm_num)
  . -- If n = 2, 3, 4, 6, 12, then n satisfies the equation.
    simp
    intro hn
    refine ⟨?_, ?_⟩
    omega
    obtain h2 | h3 | h4 | h6 | h12 := hn
    . -- Case n = 2.
      use 64
      rw [h2]
      norm_num
      rw [<-Real.sqrt_eq_rpow, show (4096 : ℝ) = 64 ^ 2 by norm_num]
      simp
    . -- Case n = 3.
      use 16
      rw [h3]
      norm_num
      calc
        4096 ^ ((1 : ℝ) / 3) = (16 ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) := by norm_num
        _ = (16 : ℝ) := by rw [<-Real.rpow_mul]; simp; norm_num
    . -- Case n = 4.
      use 8
      rw [h4]
      norm_num
      calc
        4096 ^ ((1 : ℝ) / 4) = (8 ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by norm_num
        _ = (8 : ℝ) := by rw [<-Real.rpow_mul]; simp; norm_num
    . -- Case n = 6.
      use 4
      rw [h6]
      norm_num
      calc
        4096 ^ ((1 : ℝ) / 6) = (4 ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) := by norm_num
        _ = (4 : ℝ) := by rw [<-Real.rpow_mul]; simp; norm_num
    . -- Case n = 12.
      use 2
      rw [h12]
      norm_num
      calc
        4096 ^ ((1 : ℝ) / 12) = (2 ^ (12 : ℝ)) ^ ((1 : ℝ) / 12) := by norm_num
        _ = (2 : ℝ) := by rw [<-Real.rpow_mul]; simp; norm_num
