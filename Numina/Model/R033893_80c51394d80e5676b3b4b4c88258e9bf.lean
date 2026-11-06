import Mathlib

theorem number_theory_213971 (k : ℕ) (h : 0 < k) :
    ∃ clips_at_step : ℕ → ℕ, 
    (clips_at_step 0 = 0) ∧ 
    (clips_at_step 1 = 2) ∧ 
    (clips_at_step 2 = 3) ∧ 
    (∀ n > 2, clips_at_step (n+1) = clips_at_step n + 2^(n-1)) ∧
    clips_at_step k = 2^(k-1) + 1 := by 
  use fun n => if n = 0 then 0 else 2^(n - 1) + 1
  constructor
  · -- Show that `clips_at_step 0 = 0`
    simp
  constructor
  · -- Show that `clips_at_step 1 = 2`
    simp
    <;> try { tauto }
    <;> try { omega }
  constructor
  · -- Show that `clips_at_step 2 = 3`
    simp
    <;> try { tauto }
    <;> try { omega }
  constructor
  · -- Show that `∀ n > 2, clips_at_step (n+1) = clips_at_step n + 2^(n-1)`
    intro n hn
    have h2 : n > 2 := hn
    have h3 : n + 1 > 2 := by linarith
    -- Show that n is not 0
    have h4 : n ≠ 0 := by 
      linarith
    -- Show that n+1 is not 0
    have h5 : n + 1 ≠ 0 := by 
      linarith
    simp [h4, h5, Nat.add_sub_cancel, pow_succ, pow_zero] at *
    all_goals try { tauto }
    all_goals try { 
      have h7 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        cases n with
        | zero => omega -- Contradicts h2
        | succ n' => 
          cases n' with
          | zero => omega -- Contradicts h2
          | succ n'' => 
            simp [pow_succ, pow_zero, Nat.add_sub_cancel, mul_comm]
            <;> try { ring_nf <;> try { omega } }
            all_goals try { tauto }
            <;> try { 
              exfalso <;> try { tauto } 
            }
      omega
    }
    all_goals try { 
      nlinarith [pow_pos (show 0 < 2 by norm_num) n, pow_pos (show 0 < 2 by norm_num) (n - 1)]
    }
  · -- Show that `clips_at_step k = 2^(k-1) + 1`
    simp at *
    all_goals try { tauto }
    all_goals try { 
      have h7 : k ≠ 0 := by linarith
      simp [h7] 
      all_goals try { tauto }
    }
    all_goals try { omega }
    all_goals try { 
      nlinarith [pow_pos (show 0 < 2 by norm_num) k, pow_pos (show 0 < 2 by norm_num) (k - 1)]
    }
    all_goals try { tauto }
    all_goals try { 
      exfalso <;> try { tauto } 
      <;> try { tauto }
    }
    all_goals try { tauto }
    all_goals try { 
      exfalso <;> try { tauto } 
      <;> try { tauto }
    }
    all_goals try { tauto }
    all_goals try { 
      exfalso <;> try { tauto } 
      <;> try { tauto }
    }
    all_goals try { tauto }
    all_goals try { 
      exfalso <;> try { tauto } 
      <;> try { tauto }
    }
    all_goals try { tauto }
    all_goals try { 
      exfalso <;> try { tauto } 
      <;> try { tauto }
    }
    all_goals try { tauto }
    all_goals try { 
      nlinarith [pow_pos (show 0 < 2 by norm_num) k, pow_pos (show 0 < 2 by norm_num) (k - 1)]
    }
    all_goals try { tauto }
    all_goals try { 
      nlinarith [pow_pos (show 0 < 2 by norm_num) k, pow_pos (show 0 < 2 by norm_num) (k - 1)]
    }