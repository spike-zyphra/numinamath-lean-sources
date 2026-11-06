import Mathlib

theorem number_theory_237230 {a b : ℕ} (ha : IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = 12} a)
(hb : IsLeast {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = 21} b):
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = 12} 930 ∧
    IsLeast {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).sum = 21} 399 ∧ 
    930 - 399 = 531 := by 
  constructor
  · -- first goal to prove a = 930
    constructor
    -- first prove 930 in this set.
    · simp
    · unfold upperBounds
      simp
      intro a ha ha' hassum
      by_contra h'
      simp at h'
      interval_cases a 
      iterate 69 simp at hassum
  constructor
  · -- second goal, prove b = 399
    constructor
    -- first prove 399 is in this set.
    simp
    -- then prove 399 is the least
    unfold lowerBounds
    simp
    intro a ha ha' ha₁
    by_contra h'
    simp at h'
    interval_cases a
    -- discuss case by case but every step is trivial.
    iterate 99 simp at ha₁
    iterate 100 simp at ha₁
    iterate 100 simp at ha₁
  norm_num