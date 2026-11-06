import Mathlib

theorem number_theory_16401 (f : ℕ → ℕ) (x : ℕ) (hf : f = fun y => y ^ 2 % 11) (hx : x = 5) :
    IsLeast {m | 0 < m ∧ f^[m] x = x} 4 := by 
  rw [hf, hx]
  constructor
  · -- Show that 4 is in the set, i.e., f^4(5) = 5 and 4 > 0
    constructor
    · -- Show that 0 < 4
      norm_num
    · -- Show that f^4(5) = 5
      simp [Function.iterate_succ_apply', pow_succ, Nat.pow_mod]
      all_goals norm_num
  · -- Show that 4 is the least element in the set
    intro m hm
    rcases hm with ⟨hm_pos, hm_eq⟩
    by_contra h
    push_neg at h
    interval_cases m <;> try { contradiction } <;> all_goals { simp_all [Function.iterate_succ_apply', pow_succ, Nat.pow_mod] }
    all_goals try { contradiction }
    <;> try { omega }
    <;> try { linarith }
    <;> try { simp_all }