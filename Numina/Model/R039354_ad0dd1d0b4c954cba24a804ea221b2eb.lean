import Mathlib


theorem algebra_302528 {m n : ℕ} (h : (m * n + 9 * m + 11 * n + 145) % (m + 11) = 0)
    (h' : (m * n + 9 * m + 11 * n + 145) % (9 + n) = 0) (h'' : (m * n + 9 * m + 11 * n + 145) /
    (m + 11) = (m * n + 9 * m + 11 * n + 145) / (n + 9)) : (m * n + 9 * m + 11 * n + 145) / (m + 11)
    = 25 ∨ (m * n + 9 * m + 11 * n + 145) / (m + 11) = 47 := by
  have eq1 : m * n + 9 * m + 11 * n + 145 = (m + 11) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) := by
    have h16 : (m * n + 9 * m + 11 * n + 145) % (m + 11) = 0 := h
    have eq2 : (m * n + 9 * m + 11 * n + 145) = (m + 11) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) + ((m * n + 9 * m + 11 * n + 145) % (m + 11)) := by 
      rw [Nat.div_add_mod ((m * n + 9 * m + 11 * n + 145)) (m + 11)]
    rw [h16] at eq2
    omega
  have eq4 : m * n + 9 * m + 11 * n + 145 = (n + 9) * ((m * n + 9 * m + 11 * n + 145) / (n + 9)) := by
    have h16' : (m * n + 9 * m + 11 * n + 145) % (9 + n) = 0 := by 
      omega
    have eq5' : (m * n + 9 * m + 11 * n + 145) = (9 + n) * ((m * n + 9 * m + 11 * n + 145) / (9 + n)) + ((m * n + 9 * m + 11 * n + 145) % (9 + n)) := by 
      rw [Nat.div_add_mod ((m * n + 9 * m + 11 * n + 145)) (9 + n)]
    rw [h16'] at eq5'
    have eq5'' : (9 + n) = (n + 9) := by ring
    rw [eq5''] at eq5'
    omega
  have eq9 : (m + 11) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) = (n + 9) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) := by
    have h20 : (m * n + 9 * m + 11 * n + 145) / (m + 11) = (m * n + 9 * m + 11 * n + 145) / (n + 9) := h''
    have eq7 : (m * n + 9 * m + 11 * n + 145) / (n + 9) = (m * n + 9 * m + 11 * n + 145) / (m + 11) := by 
      omega
    have eq8 : (n + 9) * ((m * n + 9 * m + 11 * n + 145) / (n + 9)) = (n + 9) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) := by 
      rw [eq7]
    have eq10 : (m * n + 9 * m + 11 * n + 145) = (n + 9) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) := by
      nlinarith [eq4, eq8]
    nlinarith [eq1, eq10]
  have eq10 : m + 11 = n + 9 := by
    have h32 : (m + 11) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) = (n + 9) * ((m * n + 9 * m + 11 * n + 145) / (m + 11)) := eq9
    have h24 : (m * n + 9 * m + 11 * n + 145) / (m + 11) ≠ 0 := by
      have h34 : (m * n + 9 * m + 11 * n + 145) ≥ 145 := by
        nlinarith [sq_nonneg (m : ℕ), sq_nonneg (n : ℕ)]
      have h44 : (m * n + 9 * m + 11 * n + 145) ≥ (m + 11) := by
        nlinarith [sq_nonneg (m : ℕ), sq_nonneg (n : ℕ)]
      have h54 : (m * n + 9 * m + 11 * n + 145) / (m + 11) ≥ 1 := by
        have h56 : (m + 11) > 0 := by
          omega
        have h77 : (m * n + 9 * m + 11 * n + 145) ≥ (m + 11) := by
          nlinarith
        have h77' : (m * n + 9 * m + 11 * n + 145) ≥ (m + 11) := by 
          nlinarith
        have h77'' : (m * n + 9 * m + 11 * n + 145) / (m + 11) ≥ 1 := by
          apply Nat.le_div_iff_mul_le (by omega) |>.mpr
          nlinarith
        omega
      omega
    have h30 : (m + 11) = (n + 9) := by
      apply (mul_left_inj' h24).mp
      linarith
    omega
  have eq15 : n = m + 2 := by 
    omega
  have h13 : (m + 11) ∣ 46 := by
    have eq17 : m * n + 9 * m + 11 * n + 145 = m ^ 2 + 22 * m + 167 := by 
      rw [show n = m + 2 by linarith [eq15]]
      ring_nf
    rw [eq17] at eq1
    have eq19 : (m ^ 2 + 22 * m + 167) = (m + 11) * ((m ^ 2 + 22 * m + 167) / (m + 11)) := by 
      nlinarith [eq1]
    have h18 : (m + 11) ∣ (m ^ 2 + 22 * m + 167) := by
      rw [eq19]
      use ((m ^ 2 + 22 * m + 167) / (m + 11))
      all_goals nlinarith
    have h19 : (m + 11) ∣ 46 := by
      have h20 : (m + 11) ∣ (m ^ 2 + 22 * m + 167) := h18
      have h21 : (m + 11) ∣ ((m + 11) * (m + 11)) := by 
        use (m + 11)
        all_goals ring_nf
      have eq23 : (m ^ 2 + 22 * m + 167) = (m + 11) * (m + 11) + 46 := by
        ring_nf
      have h24 : (m + 11) ∣ ((m ^ 2 + 22 * m + 167) - (m + 11) * (m + 11)) := by
        apply Nat.dvd_sub'
        · exact h20
        · exact h21
      rw [show (m ^ 2 + 22 * m + 167) - (m + 11) * (m + 11) = 46 by 
        rw [eq23]
        all_goals simp
      ] at h24
      exact h24
    exact h19
  have h14 : (m + 11) = 23 ∨ (m + 11) = 46 := by
    have h24 : (m + 11) ∣ 46 := h13
    have h34 : (m + 11) ≤ 46 := by
      exact Nat.le_of_dvd (by omega) h24
    interval_cases h36 : (m + 11) <;> omega
  rcases h14 with (h15 | h16)
  · -- case m + 11 = 23, so m = 12
    have h17 : m = 12 := by
      omega
    have h18 : (m * n + 9 * m + 11 * n + 145) / (m + 11) = 25 := by
      have h20 : m = 12 := h17
      have h21 : n = 14 := by
        nlinarith [eq15, h20]
      subst m n
      all_goals norm_num
    left
    omega
  · -- case m + 11 = 46, so m = 35
    have h17 : m = 35 := by
      omega
    have h18 : (m * n + 9 * m + 11 * n + 145) / (m + 11) = 47 := by
      have h20 : m = 35 := h17
      have h21 : n = 37 := by
        nlinarith [eq15, h20]
      subst m n
      all_goals norm_num
    right
    omega