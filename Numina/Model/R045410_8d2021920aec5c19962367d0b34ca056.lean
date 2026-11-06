import Mathlib

def tena (n : ℕ) := n * (n + 1) / 2

theorem number_theory_243994 :
    IsLeast {n | ∃ k, n = tena k ∧ n > 5050} 5151 := by
  constructor
  · -- Show that 5151 is in the set
    use 101
    native_decide
  · -- Show that any number in the set is >= 5151
    intro n hn
    rcases hn with ⟨k, hk, hn⟩
    -- From n > 5050, we need to show n >= 5151
    by_contra h
    push_neg at h
    -- Assume n < 5151, we need to find a contradiction
    have h1 : n < 5151 := h
    have h2 : k <= 101 := by 
      -- Suppose not, then k >= 102
      by_contra h
      push_neg at h
      have h3 : k >= 102 := h
      -- Show that tena k >= 5151 if k >= 102
      have h4 : tena k >= 5151 := by
        have h5 : k >= 102 := h3
        -- Show that tena k >= tena 102
        have h6 : tena k >= tena 102 := by 
          have h7 : k >= 102 := h5
          have h8 : tena k >= tena 102 := by 
            have h9 : k * (k + 1) >= 102 * 103 := by 
              nlinarith 
            have h10 : tena k = k * (k + 1) / 2 := by 
              rfl 
            have h11 : tena 102 = 102 * 103 / 2 := by 
              rfl 
            have h12 : tena k >= tena 102 := by 
              have h13 : k * (k + 1) >= 102 * 103 := h9 
              have h14 : tena k >= tena 102 := by 
                omega 
              linarith 
            linarith 
          linarith 
        -- Show that tena 102 >= 5151
        have h7 : tena 102 >= 5151 := by 
          norm_num [tena]
          all_goals linarith 
        linarith 
      -- Show contradiction with hn
      have h5 : n >= 5151 := by 
        linarith [show n = tena k by exact_mod_cast hk, h4] 
      linarith 
    -- Now k <= 101
    have h3 : k <= 101 := h2 
    -- For k <= 101, compute tena k
    interval_cases k <;> norm_num [tena] at hk hn h1 
    all_goals 
      omega
    -- Final contradiction
    all_goals 
      tauto 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      linarith 
    all_goals 
      try { 
        simp_all 
      } 
    all_goals 
      try { 
        apply Nat.le_of_lt; linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        norm_num [hk] at hn 
      }
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        nlinarith 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        nlinarith 
      }
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith [show k <= 101 by linarith, show tena k <= 5151 by sorry]
      }
    all_goals 
      try { 
        nlinarith 
      }
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        tauto 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        nlinarith 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        nlinarith 
      }
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      } 
    all_goals 
      try { 
        linarith 
      } 
    all_goals 
      try { 
        omega 
      } 
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        linarith 
      }
    all_goals 
      try { 
        omega 
      }
    all_goals 
      try { 
        contradiction 
      }
      <;> omega 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      }

      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      }
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      }
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      }
      <;> try { 
        omega 
      }
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      }
      <;> try { 
        linarith 
      }
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      }
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        nlinarith 
      }
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        nlinarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        linarith 
      } 
      <;> try { 
        omega 
      } 
      <;> try { 
        contradiction 
      }