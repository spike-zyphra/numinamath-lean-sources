import Mathlib

/- Determine all positive integers $n$ with the property that the third root of $n$ is obtained by removing the last three decimal digits of $n$. -/
theorem number_theory_240895 :
    {n : ℕ | 0 < n ∧ ∃ m : ℕ, m ^ 3 = n ∧ n / 1000 = m} = {32768} := by
  -- Simplify the goal into two parts.
  ext n
  apply Iff.intro
  . -- First show that the condition implies that n = 32768.
    rintro ⟨h₁, m, h₂, h₃⟩
    -- We have 1000 * m ≤ m ^ 3.
    have h₄ : 1000 * m ≤ m ^ 2 * m := by
      calc
        _ ≤ n := by
          rw [<-h₃]
          apply Nat.mul_div_le
        _ = m ^ 2 * m := by
          rw [<-h₂]
          ring
    rw [mul_le_mul_right (by nlinarith)] at h₄
    -- We have m ≥ 32.
    replace h₄ : m ≥ 32 := by
      nlinarith
    -- We also have m³ < 1000(m + 1).
    have h₅ : m ^ 2 * m < 1000 * (m + 1) := by
      calc
        _ = n := h₂
        _ < 1000 * (n / 1000 + 1) := by
          apply Nat.lt_mul_div_succ _ (by norm_num)
        _ = 1000 * (m + 1) := by
          rw [h₃]
    -- We have m < 33.
    qify at h₅
    rw [<-lt_div_iff₀ (by simp; nlinarith)] at h₅
    replace h₅ : m ^ 2 < 33 ^ 2 := by
      qify
      calc
        m ^ 2 < 1000 * (m + 1 : ℚ) / m := h₅
        _ = 1000 * (1 + 1 / m) := by
          field_simp
        _ ≤ 1000 * (1 + 1 / 32) := by
          rw [mul_le_mul_left (by norm_num)]
          apply add_le_add_left
          rw [div_le_div_iff₀ (by simp; nlinarith)]
          norm_num
          exact h₄
          norm_num
        _ < 33 ^ 2 := by
          norm_num
    -- Therefore, we have m = 32 and n = 32768.
    replace h₅ : m = 32 := by
      nlinarith
    simp [<-h₂, h₅]
  . -- Show that n = 32768 satisfies the condition.
    simp
    intro hn
    norm_num [hn]
    