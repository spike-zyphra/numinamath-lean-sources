import Mathlib

/-What is the smallest integer value of $b$ such that $423_{10}$ expressed in base $b$ also has $3$ digits?-/
theorem number_theory_19250 :
    IsLeast {b | (Nat.digits b 423).length = 3} 8 := by
  -- simplify the desired conclusion
  simp [IsLeast, lowerBounds]
  intro b hb
  cases b with
  | zero => -- when b = 0
    norm_num at hb
  | succ b => -- when 0 < b
    cases b with
    | zero => -- when b = 1
      norm_num at hb
    | succ b => -- when 1 < b
      rw [Nat.digits_len] at hb
      pick_goal 2
      . linarith only
      -- show that Nat.log (b + 1 + 1) 423 = 2
      . replace hb : Nat.log (b + 1 + 1) 423 = 2 := by linarith only [hb]
        rw [Nat.log_eq_iff] at hb
        obtain ⟨_, hb2⟩ := hb
        -- show that 7 ^ 3 < (b + 1 + 1) ^ 3
        norm_num at hb2
        replace hb2 : 7 ^ 3 < (b + 1 + 1) ^ 3 := by
          linarith only [hb2]
        -- so that 7 < b + 1 + 1
        rw [Nat.pow_lt_pow_iff_left] at hb2
        linarith only [hb2]
        -- prove some important condition
        all_goals norm_num
      norm_num