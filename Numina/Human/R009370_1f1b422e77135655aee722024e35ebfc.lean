import Mathlib

open Real

/- Find the largest positive integer $n$ such that
\[\sin^n x + \cos^n x \ge \frac{1}{n}\]for all real numbers $x.$ -/
theorem algebra_16571 :
    IsGreatest {n : ℕ | 0 < n ∧ ∀ x : ℝ, sin x ^ n + cos x ^ n ≥ 1 / n} 8 := by
  -- Break into two goals.
  simp [IsGreatest, upperBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- Show that sin x ^ 8 + cos x ^ 8 ≥ 1 / 8 for all x ∈ ℝ
    intro x
    have h₀ : 2 * (sin x ^ 8 + cos x ^ 8) ≥ (sin x ^ 4 + cos x ^ 4) ^ 2 := by
      linarith [show (sin x ^ 4 - cos x ^ 4) ^ 2 ≥ 0 by positivity]
    have h₁ : 2 * (sin x ^ 4 + cos x ^ 4) ≥ (sin x ^ 2 + cos x ^ 2) ^ 2 := by
      linarith [show (sin x ^ 2 - cos x ^ 2) ^ 2 ≥ 0 by positivity]
    rw [<-ge_iff_le]
    calc
      sin x ^ 8 + cos x ^ 8 = 4 * (2 * (sin x ^ 8 + cos x ^ 8)) / 8 := by ring_nf
      _ ≥ 4 * (sin x ^ 4 + cos x ^ 4) ^ 2 / 8 := by linarith only [h₀]
      _ = (2 * (sin x ^ 4 + cos x ^ 4)) ^ 2 / 8 := by ring_nf
      _ ≥ ((sin x ^ 2 + cos x ^ 2) ^ 2) ^ 2 / 8 := by rw [ge_iff_le, div_le_div_right (by norm_num)]; apply sq_le_sq'; simp; linarith only [show sin x ^ 4 + cos x ^ 4 ≥ 0 by positivity]; exact h₁
      _ = 1 / 8 := by simp
  . -- Show that n ≤ 8 if sin x ^ n + cos x ^ n ≥ 1 / n for all x ∈ ℝ.
    intro n npos h₀
    -- Specialize x = π in h₀. We get n even, that is, n = 2k.
    have h₁ := h₀ Real.pi
    simp [-one_div] at h₁
    norm_cast at h₁
    rw [Nat.zero_pow npos] at h₁
    simp [-one_div] at h₁
    replace h₁ : Even n := by
      by_contra! h₂
      simp [Odd] at h₂
      obtain ⟨k, h₂⟩ := h₂
      rw [h₂, pow_add] at h₁
      simp [-one_div] at h₁
      replace h₁ : 1 / (2 * k + 1 : ℝ) < 0 := by
        linarith only [h₁]
      rw [one_div_neg] at h₁
      norm_cast at h₁
    simp [Even, <-mul_two] at h₁
    obtain ⟨k, h₁⟩ := h₁
    -- Specialize x = π / 4 in h₀.
    have h₂ := h₀ (Real.pi / 4)
    simp [-one_div, h₁] at h₂
    rw [Nat.mul_comm k 2, pow_mul] at h₂
    simp [div_pow, show Real.sqrt 2 ^ 2 = 2 by norm_num, -one_div] at h₂
    norm_num
    rw [<-mul_two, <-div_pow, show (2 / 2 ^ 2 : ℝ) = 1 / 2 by norm_num, div_pow] at h₂
    simp [-one_div] at h₂
    rw [div_mul] at h₂
    nth_rewrite 3 [show (2 : ℝ) = 2 ^ 1 by norm_num] at h₂
    -- We prove that k ≤ 4, hence n ≤ 8.
    suffices h : k ≤ 4 by
      omega
    rw [h₁] at npos
    norm_num at npos
    apply le_of_one_div_le_one_div (by norm_num; exact npos) at h₂
    replace h₂ : (2 ^ k : ℝ) ≤ 4 * k := by
      calc
        (2 ^ k : ℝ) = (2 ^ k / 2 ^ 1 : ℝ) * (2 ^ 1) := by simp
        _ ≤ (k * 2 : ℝ) * 2 := by linarith only [h₂]
        _ = 4 * k := by ring_nf
    norm_cast at h₂
    contrapose! h₂
    replace h₂ : 5 ≤ k := by
      omega
    apply Nat.exists_eq_add_of_le at h₂
    obtain ⟨k', h₂⟩ := h₂
    rw [h₂]
    clear h₂
    induction k' with
    | zero =>
      simp
    | succ k' hk' =>
      rw [<-Nat.add_assoc, Nat.mul_add, Nat.pow_add]
      calc
        4 * (5 + k') + 4 * 1 < 2 ^ (5 + k') + 4 := by omega
        _ < 2 ^ (5 + k') + 2 ^ (5 + k') := by simp; rw [show 4 = 2 ^ 2 by norm_num]; rw [Nat.pow_lt_pow_iff_right]; omega; norm_num
        _ = 2 ^ (5 + k') * 2 ^ 1 := by ring_nf
