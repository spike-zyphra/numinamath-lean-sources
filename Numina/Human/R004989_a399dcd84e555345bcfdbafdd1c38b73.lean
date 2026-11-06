import Mathlib

/- Find all positive integers $n<1000$ such that the cube of the sum of the digits of $n$ equals $n^{2}$. -/
theorem number_theory_604949 :
    {n : ℕ | 0 < n ∧ n < 100 ∧ (Nat.digits 10 n).sum ^ 3 = n ^ 2} = {1, 27} := by
  -- Simplify the goal into two parts.
  ext n
  simp
  apply Iff.intro
  . -- First show that the condition implies that n = 1 or 27.
    rintro ⟨h₀, h₁, h₂⟩
    -- Let m be the sum of digits of n.
    let m := (Nat.digits 10 n).sum
    -- Show that 0 ≠ m.
    have h₃ : ¬m = 0 := by
      -- If m = 0, then n = 0.
      rw [List.sum_eq_zero_iff]
      contrapose! h₀
      rw [<-Nat.ofDigits_digits 10 n]
      simp [Nat.ofDigits_eq_sum_mapIdx]
      rw [List.sum_eq_zero_iff]
      intro x hx
      simp at hx
      obtain ⟨i, hi, hx⟩ := hx
      simp [<-hx]
      apply h₀
      simp
    -- Show that m is a square.
    have h₄ : IsSquare (m : ℚ) := by
      rw [show (Nat.digits 10 n).sum = m by rfl] at h₂
      rify at h₂
      replace h₂ := congr_arg (Real.sqrt ·) h₂
      field_simp [show (m : ℝ) ^ 3 = m * m ^ 2 by ring] at h₂
      -- Assume not, then √m is irrational, contradiction.
      by_contra!
      rw [<-irrational_sqrt_ratCast_iff_of_nonneg] at this
      absurd this
      use n / m
      field_simp [h₂]
      simp
    simp at h₄
    -- Write m = k ^ 2.
    obtain ⟨k, h₄⟩ := h₄
    -- We have k ^ 6 < 10000, so k < 5.
    have h₅ : k ^ 6 < 5 ^ 6 := by
      calc
        _ = n ^ 2 := by
          simp [<-pow_two, m] at h₄
          rw [<-h₂, h₄]
          ring
        _ < 100 ^ 2 := by
          rw [Nat.pow_lt_pow_iff_left (by norm_num)]
          exact h₁
        _ < 5 ^ 6 := by
          norm_num
    rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h₅
    -- We also have k ≠ 0.
    replace h₃ : k > 0 := by
      by_contra!
      simp at this
      simp [this, h₄] at h₃
    -- Consider all possible cases of k, which are only k = 1, 2, 3 or 4.
    interval_cases k
    <;> simp [m] at h₄
    <;> simp [h₄] at h₂
    . -- When k = 1, it corresponds to the solution n = 1.
      rw [show 1 = 1 ^ 2 by norm_num] at h₂
      apply Nat.pow_left_injective (by norm_num) at h₂
      tauto
    . -- When k = 2, n = 8 and m = 4 is contradictory.
      rw [show 64 = 8 ^ 2 by norm_num] at h₂
      apply Nat.pow_left_injective (by norm_num) at h₂
      simp [<-h₂] at h₄
    . -- When k = 3, it corresponds to the solution n = 27.
      rw [show 729 = 27 ^ 2 by norm_num] at h₂
      apply Nat.pow_left_injective (by norm_num) at h₂
      tauto
    . -- When k = 4, n = 64 and m = 16 is contradictory.
      rw [show 4096 = 64 ^ 2 by norm_num] at h₂
      apply Nat.pow_left_injective (by norm_num) at h₂
      simp [<-h₂] at h₄
  . -- Now show that n = 1 or 27 implies the condition.
    rintro (rfl | rfl)
    . -- When n = 1, the condition is satisfied.
      simp
    . -- When n = 27, the condition is satisfied.
      simp
