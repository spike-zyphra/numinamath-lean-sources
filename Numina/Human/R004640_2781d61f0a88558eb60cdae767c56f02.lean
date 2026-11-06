import Mathlib

open Nat

/- 9. 44 Let $k$ be a natural number. Determine for which value of $k$, $A_{k}=\frac{19^{k}+66^{k}}{k!}$ attains its maximum value. -/
theorem algebra_292608 {A : ℕ → ℝ} (hA : ∀ k, A k = (19 ^ k + 66 ^ k) / k !) :
    IsGreatest (Set.image A {k | 0 < k}) (A 65) := by
  simp [IsGreatest, upperBounds]
  constructor
  · use 65
    norm_num
  -- Show that for all 0 < k, A k ≤ A 65.
  intro k hk
  -- It is enough to show that A is monotone on [1, 65] and A is antitone on [65, ∞).
  suffices h : MonotoneOn A (Set.Icc 1 65) ∧ AntitoneOn A (Set.Ici 65) by
    by_cases hk : k ≤ 65
    · apply h.1 (by simp; constructor <;> omega) (by simp) hk
    simp at hk
    apply h.2 (by simp) (by simp [le_of_lt hk]) (le_of_lt hk)
  -- We have (k + 1)! * (A (k + 1) - A k) = 66 ^ k * (65 - k) - 19 ^ k * (k - 18)
  have heq k : (k + 1)! * (A (k + 1) - A k) = 66 ^ k * (65 - k) - 19 ^ k * (k - 18) := by
    simp [hA, factorial_succ, pow_succ]
    field_simp
    ring
  -- We have A i ≤ A j iff 0 ≤ (k + 1)! * (A j - A i).
  have hineq {i j} k : A i ≤ A j ↔ 0 ≤ (k + 1)! * (A j - A i) := by
    simp [mul_nonneg_iff, factorial_pos]
  constructor
  -- Show that A is monotone on [1, 65].
  · apply monotoneOn_of_le_add_one (by infer_instance)
    -- It is enough to show that A k ≤ A (k + 1) for all 1 ≤ k ≤ 64.
    simp
    intro k hk1 _ hk2
    -- We need to show that
    -- 0 ≤ 66^k * (65 - k) - 19^k * (k - 18).
    rw [hineq k, heq]
    -- Consider two cases: k ≤ 18 and 18 < k.
    by_cases h : k ≤ 18
    · rw [sub_eq_add_neg]
      -- If k ≤ 18 then 66^k * (65 - k) ≥ 0 and -19^k * (k - 18) ≤ 0.
      rify at h
      apply add_nonneg
      · apply mul_nonneg (by positivity) (by linarith)
      · simp
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    -- Assume now that 18 < k.
    simp at h
    rw [sub_nonneg]
    clear * - h hk2
    -- The proof can be completed with
    -- interval_cases k <;> norm_num.
    -- Consider a more detailed proof.
    -- We have k = k - 4 + 4, so a^k = a^(k - 4) * a^4.
    nth_rw 1 3 [show k = k - 4 + 4 by omega]
    rw [pow_add, pow_add]
    calc
      -- We have k - 18 ≤ 64 - 18.
      19^(k - 4) * 19^4 * (k - 18 : ℝ) ≤ (19^(k - 4) * (19^4 * (64 - 18)) : ℝ) := by
        rw [← mul_assoc]
        gcongr
        norm_cast
      -- 19^4 * (64 - 18) ≤ 66^4 * (65 - 64).
      _ ≤ 66^(k - 4) * (66^4 * (65 - 64)) := by
        norm_num
        gcongr <;> norm_num
      -- 65 - 64 ≤ 65 - k.
      _ ≤ 66^(k - 4) * (66^4 * (65 - k)) := by
        rify at hk2
        gcongr
      _ = 66^(k - 4) * 66^4 * (65 - k) := by ring
  -- Show that A is antitone on [65, ∞)
  · apply antitoneOn_of_add_one_le (by infer_instance)
    -- It is enough to show that A (k + 1) ≤ A k for all k ≥ 65.
    simp
    intro k hk _
    rw [hineq k, show A k - A (k + 1) = -(A (k + 1) - A k) by ring]
    rw [mul_neg, heq, neg_nonneg]
    -- We need to show that 66^k * (65 - k) - 19^k * (k - 18) ≤ 0.
    -- The result follows from 66^k * (65 - k) ≤ 0 and 0 ≤ 19^k * (k - 18).
    suffices 66 ^ k * (66 - k - 1 : ℝ) ≤ 0 ∧ 0 ≤ 19 ^ k * (k + 1 - 19 : ℝ) by
      linarith
    rify at hk
    constructor
    · apply mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    · apply mul_nonneg (by positivity) (by linarith)