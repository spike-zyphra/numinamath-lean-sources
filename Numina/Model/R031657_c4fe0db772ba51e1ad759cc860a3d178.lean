import Mathlib

theorem algebra_215731 {a b c : ℝ} (ha : a^2 + 3 * a + 1 = (b + c) / 2)
    (hb : b^2 + 3 * b + 1 = (a + c) / 2) (hc : c^2 + 3 * c + 1 = (a + b) / 2) :
    a = -1 ∧ b = -1 ∧ c = -1 := by 
  have eq1 : (a - b) * (2 * a + 2 * b + 7) = 0 := by
    nlinarith 
  have eq2 : (b - c) * (2 * b + 2 * c + 7) = 0 := by
    nlinarith 
  have eq3 : (c - a) * (2 * c + 2 * a + 7) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp eq1) with h1 h2
  · -- Case $a - b = 0$, so $a = b$
    have h1' : a = b := by linarith 
    cases' (mul_eq_zero.mp eq2) with h3 h4
    · -- Case $b - c = 0$, so $b = c$
      have h3' : b = c := by linarith 
      have ha2 : a = -1 := by
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
      have hb2 : b = -1 := by
        linarith [h1', ha2]
      have hc2 : c = -1 := by
        linarith [h3', hb2]
      exact ⟨ha2, hb2, hc2⟩
    · -- Case $2b + 2c + 7 = 0$
      -- Now we have $a = b$ from `h1'` and $2b + 2c + 7 = 0$ from `h4`
      -- Let's consider eq3
      cases' (mul_eq_zero.mp eq3) with h5 h6
      · -- Case $c - a = 0$, so $c = a$
        have h5' : c = a := by linarith 
        -- Now we have $A = b$ and $c = A$, so $a = b = c$
        -- substituting into eq (1), we get $a = -1$
        have ha2 : a = -1 := by
          nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
        have hb2 : b = -1 := by
          linarith [h1', ha2]
        have hc2 : c = -1 := by
          linarith [h5', ha2]
        exact ⟨ha2, hb2, hc2⟩
      · -- Case $2c + 2a + 7 = 0$
        -- We have $a = b$ and $2c + 2a + 7 = 0$
        -- solving will lead inconsistency
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
  · -- Case $2a + 2b + 7 = 0$
    -- Now we have `h2 : 2a + 2b + 7 = 0`
    cases' (mul_eq_zero.mp eq2) with h3 h4
    · -- Case $b - c = 0$, so $b = c$
      -- Now we have $b = c$ and $2a + 2b + 7 = 0$
      -- Let's consider eq3
      cases' (mul_eq_zero.mp eq3) with h5 h6
      · -- Case $c - a = 0$, so $c = a$
        -- Now we have $b = c = a$, and $2a + 2b + 7 = 0$
        -- which simplifies to $2a + 2a + 7 = 0$ i.e., $4a + 7 = 0$ i.e., $a = -7/4$
        -- But substituting into original equations will lead inconsistency
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
      · -- Case $2c + 2a + 7 = 0$
        -- We have $b = c$ and $2a + 2b + 7 = 0$ and $2c + 2a + 7 = 0$
        -- solving will lead inconsistency
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
    · -- Case $2b + 2c + 7 = 0$
      -- We have $2a + 2b + 7 = 0$ and $2b + 2c + 7 = 0$
      -- Let's consider eq3
      cases' (mul_eq_zero.mp eq3) with h5 h6
      · -- Case $c - a = 0$, so $c = a$
        -- We have $c = a$, $2a + 2b + 7 = 0$ and $2b + 2c + 7 = 0$
        -- solving will lead inconsistency
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]
      · -- Case $2c + 2a + 7 = 0$
        -- We have $2a + 2b + 7 = 0$, $2b + 2c + 7 = 0$ and $2c + 2a + 7 = 0$
        -- solving will lead inconsistency
        nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1)]