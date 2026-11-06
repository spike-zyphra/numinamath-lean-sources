import Mathlib
open Real

/-
Suppose a real number $x>1$ satisfies

$$
\log _{2}\left(\log _{4} x\right)+\log _{4}\left(\log _{16} x\right)+\log _{16}\left(\log _{2} x\right)=0
$$

Compute

$$
\log _{2}\left(\log _{16} x\right)+\log _{16}\left(\log _{4} x\right)+\log _{4}\left(\log _{2} x\right)
$$
-/
theorem algebra_609817 {x : ℝ} (hx : x > 1) (h: (log (log x/log 4)) /log 2 + (log (log x/log 16))/log 4 + (log (log x/log 2))/log 16 = 0)
  : (log (log x/log 16))/log 2 + (log (log x/log 4))/log 16 + (log (log x/log 2))/log 4 = -1/4 := by

  -- Some useful facts of log arithmetics
  have log_arith1: log 4 = log (2^2) := by norm_num
  have log_arith2: log 16 = log (2^4) := by norm_num
  have log_arith1': log 4 = 2 * log 2 := by
    rw [log_arith1]
    rw [log_pow]
    norm_cast
  have log_arith2': log 16 = 4 * log 2 := by
    rw [log_arith2]
    rw [log_pow]
    norm_cast

  -- The target expression equals to the following expression, since the original expression equals to 0
  have _0: (log (log x/log 16))/log 2 + (log (log x/log 4))/log 16 + (log (log x/log 2))/log 4 = (log (log x/log 16))/log 2 + (log (log x/log 4))/log 16 + (log (log x/log 2))/log 4- ((log (log x/log 4)) /log 2 + (log (log x/log 16))/log 4 + (log (log x/log 2))/log 16) := by
      rw [h]
      linarith
  rw [_0]

  -- Calculate the target expression in three parts

  -- The first part
  have _1: (log (log x/log 16))/log 2 - (log (log x/log 4)) /log 2 = -1 := by
    have logp: log x > 0 := by
      apply log_pos
      linarith
    calc
      _ = (log (log x/log 16) - log (log x/log 4))/log 2 := by simp [div_sub_div_same]
      _ = -1 := by
        rw [log_div, log_div]
        calc
          _ = (log (log 4) - log (log 16))/(log 2) := by simp
          _ = -1 := by
            rw [log_arith1', log_arith2']
            rw [log_mul, log_mul]
            field_simp
            rw [log_arith1']
            ring_nf
            linarith
            have _1: log 2 > 0 := by
              apply log_pos
              linarith

            linarith
            norm_num
            have _1: log 2 > 0 := by
              apply log_pos
              linarith
            linarith

        linarith
        norm_num
        linarith
        norm_num

  -- The second part
  have _2: (log (log x/log 4))/log 16 - (log (log x/log 2))/log 16 = -1/4 := by
    have logp: log x > 0 := by
      apply log_pos
      linarith
    calc
      _ = (log (log x/log 4) - log (log x/log 2))/log 16 := by simp [div_sub_div_same]
      _ = -1/4 := by
        rw [log_div, log_div]
        calc
          _ = (log (log 2) - log (log 4))/(log 16) := by simp
          _ = -1/4 := by
            rw [log_arith1', log_arith2']
            rw [log_mul]
            field_simp
            ring_nf
            linarith
            have _1: log 2 > 0 := by
              apply log_pos
              linarith
            linarith

        linarith
        norm_num
        linarith
        norm_num

  -- The third part
  have _3: (log (log x/log 2))/log 4 - (log (log x/log 16))/log 4 = 1 := by
    have logp: log x > 0 := by
      apply log_pos
      linarith
    calc
      _ = (log (log x/log 2) - log (log x/log 16))/log 4 := by simp [div_sub_div_same]
      _ = 1 := by
        rw [log_div, log_div]
        calc
          _ = (log (log 16) - log (log 2))/(log 4) := by simp
          _ = 1 := by
            rw [log_arith2', log_arith1', log_mul, log_arith1']
            field_simp
            linarith
            have _1: log 2 > 0 := by
              apply log_pos
              linarith
            linarith
        linarith
        norm_num
        linarith
        norm_num

  -- Combine the three parts
  calc
    _ = (log (log x /log 16) / log 2 - log (log x /log 4)/log 2) + (log (log x /log 4) / log 16 - log (log x /log 2)/log 16)  + (log (log x /log 2) /log 4 - log (log x /log 16)/log 4) := by ring_nf
    _ = -1 + 1 - 1/4 := by
      rw [_1, _2, _3]
      ring_nf
    _ = -1/4 := by norm_num
