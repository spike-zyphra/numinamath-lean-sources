import Mathlib

theorem algebra_11896 {a : ℕ → ℝ}
    (ha1 : a 1 = 1 / 2)
    (han : ∀ n ≥ 1, a n = 2 * a n * a (n + 1) + 3 * a (n + 1)) :
    ∀ n ≥ 1, a n = 1 / (3 ^ n - 1) := by
  intro n hn
  induction n with
  | zero => linarith -- base case n = 0, impossible as n ≥ 1
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
      <;> field_simp
      <;> norm_num
    | succ n =>
      have ih' := ih (by linarith)
      have h8 := han (n + 1) (by linarith)
      have h9 : a (n + 2) = a (n + 1) / (2 * a (n + 1) + 3) := by
        -- Rewrite from `h8` to get expression from term `n` to term `n+1`
        -- invert solve from `a (n+1) = 2 * a (n+1) * a (n+2) + 3 * a (n+2)`
        -- to `a (n+2) = a (n+1) / (2 * a (n+1) + 3)`
        have h10 : 2 * a (n + 1) + 3 ≠ 0 := by
          by_contra h
          have h11 : a (n + 1) = -3 / 2 := by linarith
          rw [h11] at h8
          norm_num at h8
          all_goals nlinarith [ih']
        have h12 : (2 * a (n + 1) + 3) ≠ 0 := h10
        field_simp [h12]
        nlinarith
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [h9]
      rw [ih']
      have h_pos : (3 : ℝ) ^ (n + 1) > 0 := by positivity
      have h_nonzero : (3 ^ (n + 1) - 1 : ℝ) ≠ 0 := by
        have h1 : (3 : ℝ) ^ (n + 1) > 1 := by
          have h2 : (3 : ℝ) ^ (n + 1) ≥ (3 : ℝ) ^ 1 := by
            apply pow_le_pow_right
            all_goals nlinarith
          have h3 : (3 : ℝ) ^ 1 = 3 := by norm_num
          have h4 : (3 : ℝ) > 1 := by norm_num
          nlinarith [h2, h3]
        nlinarith
      field_simp
      ring_nf
      <;> field_simp [show (3 ^ (n : ℕ) : ℝ) > 0 by positivity]
      <;> ring_nf
      <;> norm_num
      <;> try { 
        have h_zero : (3 : ℝ) ^ (n + 1) > 0 := by positivity
        nlinarith
      }
      <;> try { 
        have h_zero : (3 : ℝ) ^ (n + 1) > 0 := by positivity
        have h_zero' : (3 : ℝ) ^ (n) > 0 := by positivity
        field_simp
      }
      <;> try { 
        have h_zero : (3 : ℝ) ^ (n + 1) > 0 := by positivity
        have h_zero' : (3 : ℝ) ^ (n) > 0 := by positivity
        nlinarith
      }
      <;> try { 
        have h_zero : (3 : ℝ) ^ (n + 1) > 0 := by positivity
        have h_zero' : (3 : ℝ) ^ (n) > 0 := by positivity
        have eq1 : ( -3 * ((-1 + 3 ^ n * 3) : ℝ) + 2 * (-1 + 3 ^ n * 3)⁻¹ - 3 ^ n * 6 * (-1 + 3 ^ n * 3)⁻¹ ) = 0 := by 
          field_simp
          <;> ring
          <;> field_simp
        nlinarith [sq_nonneg ((3 ^ n) : ℝ), sq_nonneg ((3 ^ (n + 1) : ℝ)), sq_nonneg ((-1 + 3 ^ n * 3) : ℝ), h_pos, h_nonzero]
      }
      <;> try { 
        exfalso
      }
      <;> try { 
        tauto
      }
      <;> try { 
        nlinarith [sq_nonneg ((3 ^ (n + 1) - 1) : ℝ), sq_nonneg ((3 ^ (n + 1) - 1) : ℝ), h_pos, h_nonzero, sq_nonneg ((-1 + 3 ^ n * 3) : ℝ), sq_nonneg ((-1 + 3 ^ (n) * 3) : ℝ)]
      }
      all_goals try { 
          exfalso
          <;> try { 
            tauto
          }
          <;> try { 
            exfalso
            <;> tauto
          }
      }
      all_goals try { 
        exfalso
        try { exfalso <;> linarith [sq_nonneg ((3 ^ (n + 1) - 1) : ℝ), sq_nonneg ((3 ^ (n + 1) - 1) : ℝ), h_pos, h_nonzero, sq_nonneg ((-1 + 3 ^ n * 3) : ℝ), sq_nonneg ((-1 + 3 ^ n * 3) : ℝ)] }
        try { 
          have h_zero : (3 : ℝ) ^ (n) > 0 := by positivity
          linarith [sq_nonneg (a (n + 1)), sq_nonneg (a (n + 1) * a (n + 2)), sq_nonneg (a (n + 2)), sq_nonneg (a (n + 1) * a (n + 1)), sq_nonneg ((3 ^ (n + 1) - 1) * a (n + 1))]
        }
      }