import Mathlib

theorem number_theory_113270 (n : ℕ) (h : n ≠ 0) (h1 : 826 % n = 7) (h2 : 4373 % n = 8) :
    n = 9 := by 
  have h3 : n ≤ 826 := by 
    by_contra h4 
    push_neg at h4 
    have h5 : 826 % n = 826 := by 
      rw [Nat.mod_eq_of_lt] 
      all_goals linarith 
    linarith [h1, h5] 
  have h4 : n > 8 := by 
    by_contra h5 
    push_neg at h5 
    have h6 : n ≤ 8 := by linarith 
    interval_cases n <;> norm_num at h2 
    <;> try { 
      omega 
    } 
    <;> norm_num 
  interval_cases n <;> norm_num at h1 h2 <;> try { 
    try { 
      tauto 
    } 
    <;> try { 
      omega 
    } 
  } 
  <;> norm_num 
  <;> try { 
    exfalso 
    <;> try { 
      omega 
    } 
  } 
  <;> norm_num 
  <;> try { 
    exfalso 
    <;> try { 
      omega 
    } 
  } 
  <;> norm_num 
  <;> try { 
    tauto 
  } 
  <;> try { 
    norm_num 
  } 
  <;> try { 
    omega 
  }