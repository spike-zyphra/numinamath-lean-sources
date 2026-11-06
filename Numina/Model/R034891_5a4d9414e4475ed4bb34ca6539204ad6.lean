import Mathlib
set_option maxRecDepth 6000

open Finset

theorem number_theory_604999 (p : ℕ → ℕ) (hp : Set.BijOn p (range 2008) (range 2008)) (A : ℕ → ℕ)
    (A0 : A 0 = (p 0 + 1) ^ (p 0 + 1)) (hA : ∀ i ∈ range 2008, i < 2007 →
    A (i + 1) = Nat.ofDigits 10 ((Nat.digits 10 (A i)) ++ (Nat.digits 10 ((p (i + 1) + 1) ^ (p (i + 1) + 1))))) :
    ¬ IsSquare (A 2007) := by 
  have aux : ∀ n, n % 3 = 2 → ¬ IsSquare n := by
    intro n h h'; rcases h' with ⟨k, hk⟩
    rw [hk, Nat.mul_mod] at h; have := Nat.mod_lt k (show 3>0 by simp)
    interval_cases k % 3; all_goals simp at h
  apply aux; rw [Nat.modEq_three_digits_sum]
  have sumdig : (Nat.digits 10 (A 2007)).sum = ∑ i ∈ range 2008, (Nat.digits 10 ((i + 1) ^ (i + 1))).sum := by
    have mpos : 1 < 2008 := by simp
    rw [show 2007 = 2008-1 by simp] at *; generalize 2008 = m at mpos hA hp
    suffices : (Nat.digits 10 (A (m - 1))).sum = ∑ i ∈ range m, (Nat.digits 10 ((p i + 1) ^ (p i + 1))).sum
    · rw [this]; have : range m = image p (range m) := by
        simp [Finset.ext_iff]
        have := hp.image_eq; simp [Set.ext_iff] at this
        exact fun a => (fun {a b} => iff_comm.mp) (this a)
      -- Remove the permutation $p$ by `sum_image`
      nth_rw 2 [this]; rw [sum_image]; intro x hx y hy hxy
      rw [← hp.injOn.eq_iff]; all_goals assumption
    -- Generalize the recurrence equation with recurrence relation
    have jlt : m - 1 < m := by omega
    nth_rw 2 [show m = m-1+1 by omega]; generalize m - 1 = j at jlt
    induction j with
    | zero => simp [A0]
    | succ j ihj =>
      specialize ihj (by omega); rw [sum_range_succ, ← ihj]
      rw [hA, Nat.digits_ofDigits, List.sum_append]; simp
      intro l hl; rw [List.mem_append] at hl; rcases hl with hl|hl
      any_goals exact Nat.digits_lt_base' hl
      intro h; rw [List.getLast_append_right]
      apply Nat.getLast_digit_ne_zero; positivity
      simp; any_goals omega
  rw [sumdig]
  -- Compute this summation modulo 3, and we get the answer.
  native_decide