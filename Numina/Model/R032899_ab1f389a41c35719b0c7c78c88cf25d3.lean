import Mathlib

theorem number_theory_107308 (q : ℚ) (hq : q > 0) :
    (∃ n m : ℕ, n > 0 ∧ m > 0 ∧ n ≠ m ∧
      (q ^ n * (1 + q ^ m) = q ^ m * (1 + q ^ n))) ↔ q = 1 := by
  constructor
  · -- Forward direction: If there exist n, m such that q^n*(1 + q^m) = q^m*(1 + q^n) with n > 0, m > 0, n ≠ m, then q = 1
    rintro ⟨n, m, hn, hm, hneq, heq⟩
    have h : q ^ n = q ^ m := by
      nlinarith
    have h5 : q > 0 := hq
    have h9 : q ^ n = q ^ m := by
      linarith
    have hc : (n : ℕ) > 0 := hn
    have hd : (m : ℕ) > 0 := hm
    have h10 : ((q : ℝ) ^ (n : ℕ)) = ((q : ℝ) ^ (m : ℕ)) := by
      exact_mod_cast h9
    have h11 : (q : ℝ) > 0 := by
      exact_mod_cast hq
    have h14 : (n : ℝ) * (Real.log (q : ℝ)) = (m : ℝ) * (Real.log (q : ℝ)) := by
      have h12 : (q : ℝ) ^ (n : ℕ) = (q : ℝ) ^ (m : ℕ) := h10
      have : Real.log ((q : ℝ) ^ (n : ℕ)) = Real.log ((q : ℝ) ^ (m : ℕ)) := by
        rw [h12]
      have hn1 : Real.log ((q : ℝ) ^ (n : ℕ)) = (n : ℝ) * Real.log (q : ℝ) := by
        simp [Real.log_pow]
        all_goals linarith
      have hm1 : Real.log ((q : ℝ) ^ (m : ℕ)) = (m : ℝ) * Real.log (q : ℝ) := by
        simp [Real.log_pow]
        all_goals linarith
      linarith [hn1, hm1, this]
    have h15 : Real.log (q : ℝ) * ((n : ℝ) - (m : ℝ)) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h15) with h16 h17
    · -- Real.log q = 0, which implies q = 1.
      have h18 : Real.log (q : ℝ) = 0 := by
        linarith
      have h19 : (q : ℝ) = 1 := by
        rw [Real.log_eq_zero] at h18
        rcases h18 with (r | r | r)
        · linarith
        · linarith
        · linarith
      have hq1 : q = 1 := by
        exact_mod_cast h19
      exact hq1
    · -- (n - m) = 0 contradicts n ≠ m.
      exfalso
      have h18 : (n : ℝ) = (m : ℝ) := by linarith
      have h19 : n = m := by
        exact_mod_cast h18
      contradiction
  · -- Backward direction: If q = 1, then there exist n, m with n > 0, m > 0, n ≠ m, and q^n*(1 + q^m) = q^m*(1 + q^n)
    intro hq
    rw [hq]
    use 1, 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num