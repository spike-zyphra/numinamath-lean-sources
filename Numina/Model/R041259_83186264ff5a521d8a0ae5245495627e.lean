import Mathlib

theorem number_theory_14166 (f : ℕ+ → ℕ) (hf : ∀ n, f n = (Nat.digits 10 (2 ^ n.val)).sum) :
   IsLeast {n : ℕ+ | 10 < f n} 7 := by
  have h1 : ∀ n, f n = (Nat.digits 10 (2 ^ n.val)).sum := hf
  constructor
  · -- Show 7 is in the set
    show 10 < f 7
    rw [h1 7]
    native_decide
  · -- Show there is no smaller element in the set
    intro n hn
    have h2 : 10 < f n := by
      simpa using hn
    by_contra h
    push_neg at h
    have h3 : n.val < 7 := by
      exact h
    have h4 : f n ≤ 10 := by
      rw [h1 n]
      have h5 : n.val < 7 := h3
      interval_cases h : n.val <;> norm_num
    linarith