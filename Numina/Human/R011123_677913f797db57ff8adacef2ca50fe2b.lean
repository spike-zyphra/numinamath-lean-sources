import Mathlib

theorem algebra_224104 {a r : ℝ} (hr1 : r ≥ 0) (hsum : ∑' n : ℕ, a * r ^ n = 2) (hr2 : r < 1) (ha : a ≠ 0)
    (hsumsq : ∑' n : ℕ, (a * r ^ n) ^ 2 = 6) :
    ∑' n : ℕ, (a * r ^ n) ^ 3 = 96 / (7 : ℝ) := by 
  have neq :  1 + r ≠ 0 := by 
    by_contra hc
    have req : r = - 1 := by linarith
    linarith
  have neq2 : ((1 - r ^ 2) * a ^ 2) ≠ 0 := by 
    have aux : (1 - r ^ 2) ≠ 0 := by 
      by_contra hc
      have req_aux : r = 1 ∨ r = -1 := by 
        have req : r ^ 2 = 1 := by
          linarith
        exact sq_eq_one_iff.mp req
      obtain aux1 | aux2 := req_aux
      linarith
      linarith
    have aneq : a ^ 2 ≠ 0 := by   
      exact pow_ne_zero 2 ha
    exact (mul_ne_zero_iff_right aneq).mpr aux
  have eq1 : ∑' n : ℕ, a * r ^ n = a / (1 - r) := by 
    calc 
      
      _ = a * ∑' n : ℕ, ((r) ^ n) := by 
        exact tsum_mul_left
      _ = a * (1 / (1 - (r))) := by 
        congr
        simp
        refine (tsum_geometric_of_lt_one ?_ ?_)
        positivity
        nlinarith
      _ = a / (1 - r) := by field_simp
  have eq2 : ∑' n : ℕ, (a * r ^ n) ^ 2 = a ^ 2 / (1 - r ^ 2):= by 
    calc 
      _ = ∑' n : ℕ, (a ^ 2 * (r ^ 2) ^ n)  := by 
        congr
        funext n
        rw [mul_pow]
        field_simp
        rw [←pow_mul, ←pow_mul]
        rw [mul_comm 2 n]
      _ = a ^ 2 * ∑' n : ℕ, ((r ^ 2) ^ n) := by 
        exact tsum_mul_left
      _ = a ^ 2 * (1 / (1 - (r ^ 2))) := by 
        congr
        simp
        refine (tsum_geometric_of_lt_one ?_ ?_)
        positivity
        nlinarith
      _ = a ^ 2 / (1 - r ^ 2) := by field_simp

  have eq3 : ∑' n : ℕ, (a * r ^ n) ^ 3 = a ^ 3 / (1 - r ^ 3) := by 
    calc 
      _ = ∑' n : ℕ, (a ^ 3 * (r ^ 3) ^ n)  := by 
        congr
        funext n
        rw [mul_pow]
        field_simp
        rw [←pow_mul, ←pow_mul]
        rw [mul_comm 3 n]
      _ = a ^ 3 * ∑' n : ℕ, ((r ^ 3) ^ n) := by 
        exact tsum_mul_left
      _ = a ^ 3 * (1 / (1 - (r ^ 3))) := by 
        congr
        simp
        refine (tsum_geometric_of_lt_one ?_ ?_)
        positivity
        nlinarith
      _ = a ^ 3 / (1 - r ^ 3) := by field_simp
  have eq4 : (a / (1 - r) ) ^ 2 = 4 := by 
    rw [hsum] at eq1
    rw [←eq1]
    norm_num
  have eq5 : a ^ 2 / (1 - r ^ 2) = 6 := by 
    rw [hsumsq] at eq2
    exact Eq.symm eq2
  have eq6 : (1 - r ^ 2) = (1 - r) * (1 + r) := by ring
  have eq7 : (1 - r) / (1 + r) = 3 / 2 := by 
    rw [hsum] at eq1
    rw [hsumsq] at eq2
    calc 
      _ = (a ^ 2 / (1 - r ^ 2)) / ((a / (1 - r)) ^ 2) := by 
        field_simp
        ring
      _ = 3 / 2 := by 
        rw [←eq2, eq4]
        norm_num
  
  have eq8 : r = - 1 / 5 := by
    field_simp at eq7
    linarith
  have aeq : a = 12 / 5 := by 
    rw [eq1, eq8] at hsum
    field_simp at hsum
    linarith
  rw [eq3, eq8, aeq]
  field_simp
  ring