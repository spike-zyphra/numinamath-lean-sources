import Mathlib

theorem algebra_54292 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℂ → ℂ) (hf : ∀ z, f z = (a + b * Complex.I) * z)
    (h : ∀ z, Complex.abs (f z - z) = Complex.abs (f z)) (h' : Complex.abs (a + b * Complex.I) = 8)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (h'' : b ^ 2 = m / n) :
    m + n = 259 := by

  have eq1 := h 1

  simp [hf] at eq1

  have eq2 : Complex.abs ((a + b * Complex.I) - 1) = Complex.abs (a + b * Complex.I) := by
    simpa using eq1

  have eq3 : Complex.abs ((a + b * Complex.I) - 1) = Real.sqrt ((a - 1) ^ 2 + b ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring

  have eq4 : Complex.abs (a + b * Complex.I) = Real.sqrt (a ^ 2 + b ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring

  rw [eq3, eq4] at eq2

  have eq5 : (a - 1) ^ 2 + b ^ 2 = a ^ 2 + b ^ 2 := by
    have h1 : Real.sqrt ((a - 1) ^ 2 + b ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) := eq2
    have h2 : (a - 1) ^ 2 + b ^ 2 ≥ 0 := by
      positivity
    have h3 : a ^ 2 + b ^ 2 ≥ 0 := by
      positivity
    have h4 : (a - 1) ^ 2 + b ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Real.sqrt_inj (by positivity) (by positivity) ] at h1
      linarith
    linarith

  have ha_eq : a = 1 / 2 := by
    nlinarith

  have h_mod : Complex.abs (a + b * Complex.I) = Real.sqrt (a ^ 2 + b ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    ring

  rw [h_mod] at h'
  have h_abs : Real.sqrt (a ^ 2 + b ^ 2) = 8 := h'

  have h_abs2 : a ^ 2 + b ^ 2 = 64 := by
    calc
      a ^ 2 + b ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 8 ^ 2 := by rw [h_abs]
      _ = 64 := by norm_num

  rw [show a = 1 / 2 by linarith [ha_eq]] at h_abs2
  have hb2 : b ^ 2 = 255 / 4 := by
    nlinarith

  have eq6 : (b ^ 2 : ℝ) = (m : ℝ) / (n : ℝ) := by
    exact_mod_cast h''

  rw [hb2] at eq6

  have eq7 : (m : ℝ) / (n : ℝ) = (255 : ℝ) / (4 : ℝ) := by
    linarith [eq6]

  have eq8 : (m : ℝ) * 4 = 255 * (n : ℝ) := by
    field_simp at eq7 ⊢
    nlinarith

  have eq9 : m * 4 = 255 * n := by
    exact_mod_cast eq8

  have h1 : m * 4 = 255 * n := by
    linarith [eq9]

  have h2 : m = 255 := by
    have h1 : m * 4 = 255 * n := eq9
    have h3 : Nat.Coprime m n := hmn
    have h4 : m ∣ 255 := by
      have h5 : m ∣ 255 * n := by
        use 4
        linarith
      have h6 : m ∣ 255 := by
        apply Nat.Coprime.dvd_of_dvd_mul_right hmn
        assumption
      assumption
    have h7 : m = 255 := by
      have h8 : m ∣ 255 := h4
      have h9 : m ≤ 255 := by
        exact Nat.le_of_dvd (by norm_num) h8
      interval_cases m <;> omega
    assumption

  have h3 : n = 4 := by
    nlinarith [h1, h2]

  calc
    m + n = 255 + 4 := by rw [h2, h3]
    _ = 259 := by norm_num