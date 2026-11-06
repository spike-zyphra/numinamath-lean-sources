import Mathlib

theorem number_theory_5737 (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n)
    (h : 3 * m + 5 * n = 79) : m + n = 25 := by 
  have h1 : n ≤ 15 := by 
    omega 
  have h2 : m ≤ 26 := by 
    omega 
  interval_cases n <;> try { 
    try { 
      interval_cases m <;> norm_num at h hm hn ⊢ <;> try { tauto } 
    } 
    <;> try { 
      contradiction 
    } 
  }
  <;> try { 
    try { 
      contradiction 
    } 
    <;> try { 
      omega 
    } 
  }
  <;> try { try { contradiction } } 
  <;> try { try { omega } }
  <;> try { 
    try { 
      native_decide 
    } 
    <;> try { 
      trivial 
    } 
  }
  <;> try { try { 
    native_decide 
    <;> try { 
      trivial 
    } 
  } }