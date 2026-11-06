import Mathlib

theorem algebra_237357 {a : ℕ → ℝ}
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = (1 + 4 * a n + Real.sqrt (1 + 24 * a n)) / 16) :
  ∀ n ≥ 1, a n = (1 / 3) + (1 / 2)^n + (2 / 3) * (1 / 4)^n := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n => 
      have h1 := ih (by linarith)
      have eq1 : a (n + 2) = (1 + 4 * a (n + 1) + Real.sqrt (1 + 24 * a (n + 1)))/16 := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [eq1]
      rw [h1]
      have h_eq2 : Real.sqrt ((1 : ℝ) + 24 * ((1 / 3) + (1 / 2) ^ (n + 1) + (2 / 3) * (1 / 4) ^ (n + 1) ) ) = 3 + 4 * (1 / 2) ^ (n + 1) := by
        have h_eq1 : (1 + 24 * ((1 / 3) + (1 / 2) ^ (n + 1) + (2 / 3) * (1 / 4) ^ (n + 1) : ℝ)
          ) = (3 + 4 * (1 / 2) ^ (n + 1) ) ^ 2 := by
          have eq3 : ((1 / 4) : ℝ) ^ (n + 1) = (1 / 2) ^ (2 * (n + 1)) := by
            rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
            rw [← pow_mul]
            <;> ring_nf
            all_goals tauto
          rw [eq3]
          ring_nf
          <;> norm_num
          <;> ring_nf
          <;> norm_num
          <;> ring_nf
          <;> norm_num
          all_goals 
            try { 
              field_simp
              <;> ring_nf
              <;> norm_num
            }
            try { 
                tauto 
            }
          all_goals 
            try { 
                linarith
            }
          all_goals 
            try { 
              nlinarith
            }
        have h_eq2 : Real.sqrt ((1 + 24 * ((1 / 3) + (1 / 2) ^ (n + 1) + (2 / 3) * (1 / 4) ^ (n + 1) : ℝ)) ) = (3 + 4 * (1 / 2) ^ (n + 1) ) := by
          rw [h_eq1]
          have h_pos : (0 : ℝ) ≤ (3 + 4 * (1 / 2) ^ (n + 1) ) := by
            positivity
          rw [Real.sqrt_sq (by positivity)]
        exact h_eq2
      rw [h_eq2]
      field_simp
      ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      all_goals
        try { 
          ring_nf <;> norm_num
        }
        try { 
            tauto
        }
        try { 
          nlinarith
        }
  all_goals tauto
  all_goals try { 
    nlinarith 
  }