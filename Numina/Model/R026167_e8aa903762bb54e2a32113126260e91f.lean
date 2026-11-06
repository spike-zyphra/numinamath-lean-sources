import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_110662 {f1 f2 f3 : ℝ → ℝ}
  (hf1 : ∀ x, 0 ≤ x → f1 x = x)
  (hf2 : ∀ x, 0 ≤ x → f2 x = 2 ^ x - 1)
  (hf3 : ∀ x, 0 ≤ x → f3 x = Real.log (x + 1)) :
  (∀ x, 0 ≤ x → 0 ≤ f1 x) ∧ (∀ x, 0 ≤ x → 0 ≤ f2 x) ∧
  (∀ s t, 0 ≤ s → 0 ≤ t → f1 s + f1 t ≤ f1 (s + t)) ∧
  (∀ s t, 0 ≤ s → 0 ≤ t → f2 s + f2 t ≤ f2 (s + t)) ∧
  ¬(∀ s t, 0 ≤ s → 0 ≤ t → f3 s + f3 t ≤ f3 (s + t)) := by
  constructor
  · -- Show that f1(x) ≥ 0 when x ≥ 0
    intro x hx
    have h1 : f1 x = x := hf1 x hx
    rw [h1]
    linarith
  constructor
  · -- Show that f2(x) ≥ 0 when x ≥ 0
    intro x hx
    have h2 : f2 x = (2 : ℝ) ^ x - 1 := hf2 x hx
    rw [h2]
    have h3 : (2 : ℝ) ^ x ≥ 1 := by
      apply Real.one_le_rpow
      all_goals nlinarith
    linarith
  constructor
  · -- Show that f1(s) + f1(t) ≤ f1(s + t) for all s, t ≥ 0
    intro s t hs ht
    have h1s : f1 s = s := hf1 s hs
    have h1t : f1 t = t := hf1 t ht
    have h1st : f1 (s + t) = s + t := by
      apply hf1
      linarith
    rw [h1s, h1t, h1st]
    all_goals linarith
  constructor
  · -- Show that f2(s) + f2(t) ≤ f2(s + t) for all s, t ≥ 0
    intro s t hs ht
    have h2s : f2 s = (2 : ℝ) ^ s - 1 := hf2 s hs
    have h2t : f2 t = (2 : ℝ) ^ t - 1 := hf2 t ht
    have h2st : f2 (s + t) = (2 : ℝ) ^ (s + t) - 1 := by
      apply hf2
      linarith
    rw [h2s, h2t, h2st]
    have h3 : (2 : ℝ) ^ (s + t) = (2 : ℝ) ^ s * (2 : ℝ) ^ t := by
      rw [Real.rpow_add]
      all_goals linarith
    rw [h3] at *
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by linarith) s, Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by linarith) t,
              Real.one_le_rpow (show (1 : ℝ) ≤ (2 : ℝ) by linarith) (show 0 ≤ s by linarith), 
              Real.one_le_rpow (show (1 : ℝ) ≤ (2 : ℝ) by linarith) (show 0 ≤ t by linarith)]
  · -- Show that f3(x) does not satisfy the condition
    intro h
    have h31 := h 1 1 (by norm_num) (by norm_num)
    have h41 : f3 (1 : ℝ) = Real.log 2 := by 
      specialize hf3 1 (by norm_num)
      norm_num at hf3 ⊢ 
      linarith 
    have h42 : f3 (1 + 1 : ℝ) = Real.log 3 := by 
      specialize hf3 (1 + 1) (by norm_num)
      norm_num at hf3 ⊢ 
      linarith
    rw [h41] at h31 
    rw [h42] at h31
    have h5 : 2 * Real.log 2 = Real.log 4 := by 
      calc 
        2 * Real.log 2 = Real.log ((2 : ℝ) ^ 2) := by simp [Real.log_pow]
        _ = Real.log (4 : ℝ) := by norm_num
    have h6 : Real.log (4 : ℝ) > Real.log (3 : ℝ) := by
      apply Real.log_lt_log
      all_goals norm_num
    linarith [h31, h5, h6]