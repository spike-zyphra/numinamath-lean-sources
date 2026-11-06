import Mathlib

theorem number_theory_217443 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (hmn : m.Coprime n) (h : (144 / 10000 : ℚ) = m / n) :
    m + n = 634 := by
-- Rewrite the equation to 144 * n = 10000 * m
  have h_eq : 144 * (n : ℚ) = 10000 * (m : ℚ) := by
    field_simp at h
    linarith

-- Rewriting to natural numbers.
  have h_eq_nat : 144 * n = 10000 * m := by
    exact_mod_cast h_eq
-- Simplify to 9n = 625m
  have h4 : 9 * n = 625 * m := by
    omega

  have h5 : m ∣ 9 * n := by
    use 625
    linarith
  have h6 : m ∣ 9 := by
    have h7 : m ∣ 9 * n := by
      use 625
      linarith
    have h8 : m ∣ 9 := by
      apply Nat.Coprime.dvd_of_dvd_mul_right hmn h7
    exact h8
  have h7 : m ≤ 9 := by
    exact Nat.le_of_dvd (by norm_num) h6
-- Using interval_cases on m.
  interval_cases m <;> try { 
    omega 
    <;> try { 
      norm_num at h_eq_nat hmn <;> tauto
    }
  }
  all_goals omega