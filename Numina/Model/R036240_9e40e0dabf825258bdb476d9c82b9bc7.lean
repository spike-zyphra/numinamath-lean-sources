import Mathlib

theorem algebra_15838 (a b c T : ℤ) (hT : T ≠ 0) (hA : 0 = a * 0 ^ 2 + b * 0 + c)
    (hB : 0 = a * (2 * T) ^ 2 + b * (2 * T) + c) (hC : 28 = a * (2 * T + 1) ^ 2 + b * (2 * T + 1) + c)
    (N : ℤ) (hN : N = -b / (2 * a) + c / (a)) :
    N ≤ 60 := by
  have hc : c = 0 := by linarith
  rw [hc] at hB
  rw [hc] at hC
  have eq1 : 2 * a * T + b = 0 := by
    have h1 : 4 * a * T ^ 2 + 2 * b * T = 0 := by linarith
    have : 2 * T * (2 * a * T + b) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp this) with h2 h3
    · -- Case $2 * T = 0$, so $T = 0$, which contradicts $T ≠ 0$.
      have hT0 : T = 0 := by linarith
      contradiction
    · -- Case $2 * a * T + b = 0$.
      linarith
  have eq2 : b = -2 * a * T := by linarith
  have eq3 : a * (2 * T + 1) = 28 := by
    rw [eq2] at hC
    nlinarith [sq_nonneg (T * a), sq_nonneg ((2 * T + 1 : ℤ) * a)]
  have hN2 : N = -b / (2 * a) := by
    rw [hN, hc]
    norm_num
    <;> ring_nf <;> norm_num
  rw [hN2]
  rw [eq2]
  have h3 : a ∣ 28 := by
    use 2 * T + 1
    all_goals linarith
  have h4 : a ∣ 28 := h3
  have h5 : a ≤ 28 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h6 : a ≥ -28 := by
    have h7 : -a ∣ 28 := by
      exact Int.neg_dvd.2 h4
    have h8 : -a ≤ 28 := by
      apply Int.le_of_dvd (by norm_num) h7
    linarith
  interval_cases a <;> try { 
    omega 
  }
  all_goals 
    try { 
      norm_num 
      <;> tauto 
      <;> try { 
        omega 
      } 
      <;> try { 
        nlinarith 
      }
    }
  all_goals 
    try { 
      omega 
    }
  all_goals 
    try { 
      nlinarith [sq_nonneg ((T : ℤ) * (a : ℤ)), sq_nonneg ((2 * T + 1 : ℤ) * (a : ℤ))]
    }