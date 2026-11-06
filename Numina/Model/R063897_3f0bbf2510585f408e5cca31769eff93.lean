import Mathlib

theorem number_theory_176186 {n : ℕ} (hn : n = 2^5 * 3^3 * 5^2 * 7) :
    IsGreatest {x | x ∈ n.divisors ∧ x ∈ Finset.Icc 10 99} 96 := by
  rw [hn]
  constructor
  · -- Show 96 is in the set.
    constructor
    · -- Show 96 divides 151200.
      native_decide
    · -- Show 96 is in the interval [10, 99].
      native_decide
  · -- Show that 96 is greatest.
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    simp at hx1 hx2 ⊢
    by_contra h
    push_neg at h
    have h2 : x > 96 := h
    have h3 : x ≤ 99 := by linarith [hx2.2]
    interval_cases x <;> norm_num at hx1 <;> contradiction
    all_goals try { contradiction }
    <;> norm_num
    <;> try { norm_num at hx1 <;> contradiction }
    all_goals try { native_decide }
    <;> norm_num
    <;> try { norm_num at hx1 <;> contradiction }
    all_goals try { native_decide }