import Mathlib

theorem algebra_54443 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) (hsum1 : x + 1 / z = 5) (hsum2 : y + 1 / x = 29)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    (hsum3 : z + 1 / y = m / n) :
    m + n = 5 := by
  have h1 : z ≠ 0 := by linarith 
  have h2 : x ≠ 0 := by linarith 
  have h3 : y ≠ 0 := by linarith

  have eq1 : x * z + 1 = 5 * z := by 
    field_simp [h1] at hsum1 
    linarith

  have eq2 : y * x + 1 = 29 * x := by 
    field_simp [h2] at hsum2 
    linarith

  have eq4 : x = 1 / 5 := by
    nlinarith [hxyz, eq1, eq2, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have eq5 : y = 24 := by 
    rw [eq4] at hsum2
    field_simp at hsum2 ⊢ 
    linarith

  have eq6 : z = 5 / 24 := by 
    rw [eq4, eq5] at hxyz 
    nlinarith

  have eq7 : z + 1 / y = (1 : ℝ) / 4 := by
    rw [eq6, eq5] 
    norm_num

  rw [eq7] at hsum3

  have h8 : (m : ℝ) / (n : ℝ) = (1 : ℝ) / 4 := by 
    linarith

  have h9 : m * 4 = n := by 
    have h10 : (m : ℝ) * (4 : ℝ) = (n : ℝ) := by 
      field_simp [(show (n : ℝ) ≠ 0 by positivity), (show (4 : ℝ) ≠ 0 by norm_num)] at h8 ⊢ 
      linarith 
    norm_cast at h10 ⊢ 

  have eq8 : m = 1 := by
    have h : Nat.Coprime m n := hmn 
    rw [show n = 4 * m by omega] at h
    have h11 : m.gcd (4 * m) = m := by
      simp [Nat.gcd_mul_right, Nat.gcd_comm]

    have h12 : m.gcd (4 * m) = 1 := by 
      exact h.gcd_eq_one 

    have h112 : m = 1 := by 
      nlinarith [h11, h12]

    exact h112

  have eq9 : n = 4 := by
    omega 

  calc 
    m + n = 1 + 4 := by rw [eq8, eq9] 
    _ = 5 := by norm_num