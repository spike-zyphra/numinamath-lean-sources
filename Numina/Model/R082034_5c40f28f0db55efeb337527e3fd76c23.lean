import Mathlib

theorem number_theory_22729 :
    IsLeast {n | 0 < n ∧ 30 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 2} 2220 := by 
  constructor
  · -- Show 2220 is in the set 
    refine ⟨by norm_num, by norm_num, ?_⟩ 
    intro d hd 
    have h1 : Nat.digits 10 2220 = [0, 2, 2, 2] := by norm_num 
    have h2 : d ∈ Nat.digits 10 2220 := hd
    rw [h1] at h2
    simpa using h2
  · -- Show no smaller element is in the set 
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_dig⟩
    by_contra h
    push_neg at h 
    interval_cases n <;> norm_num at hn_div hn_pos <;> norm_num [Nat.digits, Nat.digitsAux] at hn_dig ⊢ 
      <;> try { contradiction }
      <;> try { trivial }
      <;> try { norm_num at hn_div hn_pos ⊢ }
      <;> try { contradiction }
      <;> try { trivial }
      <;> try { contradiction }
      <;> try { trivial }
      <;> try { contradiction }
      <;> try { trivial }