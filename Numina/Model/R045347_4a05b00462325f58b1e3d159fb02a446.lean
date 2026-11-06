import Mathlib

theorem number_theory_610317 (f : ℕ → ℕ) (hf : f = fun n ↦ ((n ^ 2 + 1).primeFactors.max).unbot' 0) :
    IsLeast { n | n > 0 ∧ f (f n) = n } 89 := by
  constructor
  · -- Show that 89 is in the set
    constructor
    · norm_num
    · -- Show that f(f(89)) = 89
      rw [hf]
      native_decide
  · -- Show that 89 is the least element in the set
    intro n hn
    rcases hn with ⟨hn_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h_lt : n < 89 := by linarith
    have hne : f (f n) ≠ n := by
      rw [hf]
      interval_cases n <;> try { native_decide }
    omega