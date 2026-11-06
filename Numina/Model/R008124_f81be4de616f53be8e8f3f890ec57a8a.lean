import Mathlib

theorem number_theory_14834
    (is_abundant : ℕ → Prop)
    (def_is_abundant : ∀ n, is_abundant n = (∑ d in n.properDivisors, d > n)) :
    IsLeast {n | is_abundant n ∧ ¬6 ∣ n} 20 := by
  constructor
  · constructor
    · rw [def_is_abundant]
      native_decide
    · norm_num
  · intro n hn
    rcases hn with ⟨h_abund, h_not_div_6⟩
    rw [def_is_abundant] at h_abund
    by_contra h
    push_neg at h
    have h1 : n < 20 := by linarith
    interval_cases n <;> try { contradiction }
    <;> try { contradiction }
    <;> try { native_decide }