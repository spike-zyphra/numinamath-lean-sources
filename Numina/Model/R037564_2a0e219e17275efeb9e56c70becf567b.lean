import Mathlib


theorem number_theory_13923 : IsLeast {n : ℕ | 0 < n ∧ 2016 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 2 ∧ d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6} 48384 := by
  constructor
  · -- Show 48384 is in the set.
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show that all digits of 48384 are not in {2, 0, 1, 6}
      native_decide
  · -- Show that 48384 is the smallest such element.
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_dig⟩
    by_contra h
    push_neg at h
    -- Since n is divisible by 2016 and less than 48384, so n < 48384.
    have h1 : n < 48384 := by
      linarith
    -- Since 2016 divides n, so n = 2016 * k for some k.
    rcases hn_div with ⟨k, hk⟩
    have h7 : k < 24 := by
      nlinarith
    have h9 : k > 0 := by
      by_contra h
      push_neg at h
      have : k ≤ 0 := by omega
      have : k = 0 := by omega
      rw [this] at hk
      have : n = 0 := by linarith
      linarith
    interval_cases k <;> norm_num [hk] at hn_dig hn_pos ⊢
    <;> try { 
      norm_num at hn_dig hn_pos ⊢
      all_goals
      try { 
        exfalso 
        try { 
          have h0 := hn_dig 0 (by norm_num)
          all_goals omega 
        } 
        try { 
          have h1 := hn_dig 1 (by norm_num)
          all_goals omega 
        } 
        try { 
          have h2 := hn_dig 2 (by norm_num)
          all_goals omega 
        } 
        try { 
          have h6 := hn_dig 6 (by norm_num)
          all_goals omega 
        } 
      } 
    }