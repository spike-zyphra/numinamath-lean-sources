import Mathlib

theorem number_theory_103116
    (m n p : ℕ)
    (hm : m > n)
    (hn : n > p)
    (hprime : Nat.Prime m ∧ Nat.Prime n ∧ Nat.Prime p)
    (hsum : m + n + p = 74)
    (hdiff : m - n - p = 44) :
    m = 59 ∧ n = 13 ∧ p = 2 := by

  have eq2 : m = 59 := by 
    have h2 : m ≥ n + p := by 
      omega 
    omega 
  have eq3 : n + p = 15 := by 
    omega 
  have h3 : Nat.Prime m := hprime.1
  have h4 : Nat.Prime n := hprime.2.1
  have h5 : Nat.Prime p := hprime.2.2 
  have eq5 : p ≤ 15 := by 
    omega 
  interval_cases p <;> try { 
    norm_num at h5 eq3 
    all_goals try { 
      omega 
    }
  } 
  <;> try { 
    have eq6 : n ≤ 15 := by 
      omega 
    interval_cases n <;> try { 
      norm_num at h4 eq3 
      <;> omega 
    }
  }
  <;> try { 
    omega 
  }