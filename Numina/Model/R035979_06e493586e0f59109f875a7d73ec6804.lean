import Mathlib

theorem algebra_97318 {x y z : ℝ} (m n : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) (hxz : x + 1 / z = 5) (hyx : y + 1 / x = 29)
    (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) (eq : z + 1 / y = m / n) : m + n = 5 := by

  have eq1 : x * z + 1 = 5 * z := by
    field_simp at hxz ⊢
    nlinarith

  have eq2 : x * y + 1 = 29 * x := by
    field_simp at hyx ⊢
    nlinarith

  have eq3 : x = (5 * z - 1) / z := by
    field_simp at eq1 ⊢
    nlinarith

  have eq4 : (5 * z - 1) * y = 1 := by
    have eq5 : x * y * z = 1 := hxyz
    rw [eq3] at eq5
    field_simp at eq5 ⊢
    nlinarith

  have eq6 : (5 * z - 1) * y = (29 * (5 * z - 1) ) - z := by
    have eq7 : x * y = 29 * x - 1 := by
      nlinarith
    rw [eq3] at eq7
    field_simp at eq7 ⊢
    nlinarith

  have hz' : z = 5 / 24 := by
    nlinarith

  have hy' : y = 24 := by
    have eq8 : (5 * z - 1) * y = 1 := eq4
    rw [hz'] at eq8
    nlinarith

  have eq7 : z + 1 / y = (1 : ℝ) / 4 := by
    rw [hz', hy']
    norm_num

  have h1 : (m : ℝ) / (n : ℝ) = (1 : ℝ) / 4 := by
    linarith [eq, eq7]

  have h2 : m * 4 = n := by
    have h3 : (m : ℝ) * 4 = (n : ℝ) := by
      field_simp at h1 ⊢
      nlinarith
    exact_mod_cast h3

  have h3 : m = 1 := by
    have h4 : Nat.gcd m n = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at hmn
      exact_mod_cast hmn

    have h5 : n = 4 * m := by omega

    have h6 : Nat.gcd m n = m := by
      rw [show n = 4 * m by omega]
      simp [Nat.gcd_mul_right]

    have h7 : m = 1 := by
      nlinarith [h4, h6]

    linarith

  have h4 : n = 4 := by
    nlinarith [h3, h2]

  linarith