import Mathlib

theorem number_theory_3653
    (f : ℕ → ℕ)
    (hf : ∀ n, f n = Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) :
    IsLeast {n | n ∈ Set.Icc 10 99 ∧ f n = n + 72} 19 := by
  constructor
  · -- Show that 19 is in the set
    constructor
    · -- Show that 19 is in the range [10, 99]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that f 19 = 19 + 72
      rw [hf]
      native_decide
  · -- Show that no smaller element is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Set.mem_Icc] at hn1
    rcases hn1 with ⟨h10, h99⟩
    by_contra h
    push_neg at h
    have h2 : n < 19 := by linarith
    interval_cases n <;> simp [hf, Nat.ofDigits, Nat.digits, Nat.digitsAux] at hn2 <;> all_goals omega