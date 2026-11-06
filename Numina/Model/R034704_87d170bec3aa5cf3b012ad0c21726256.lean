import Mathlib

theorem number_theory_16142 : IsLeast {b : ℕ+ | ∃ x : ℕ+, Nat.gcd b.val 50 = x.val + 5 ∧
    Nat.lcm b.val 50 = x.val * (x.val + 5)} 10 := by
  constructor
  · -- Show 10 is in the set
    use 5
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro b hb
    rcases hb with ⟨x, hx1, hx2⟩
    by_contra h
    push_neg at h
    have h1 : b.val < 10 := by
      exact_mod_cast h
    interval_cases b.val <;> try { 
      norm_num at hx1 hx2
      all_goals omega 
    }