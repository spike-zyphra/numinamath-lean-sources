import Mathlib

theorem algebra_4511 : IsGreatest {a : ℤ | ∃ m n : ℤ, m > 0 ∧ n > 0 ∧ m ≠ n ∧ m^2 + a * m + 312 = 0 ∧ n^2 + a * n + 312 = 0} (-37) := by
  constructor
  · -- Show that -37 is in the set
    use 13, 24
    all_goals norm_num
  · -- Show that if a is in the set, then a ≤ -37
    intro a ha
    rcases ha with ⟨m, n, hm, hn, hne, hm2, hn2⟩
    have h1 : (m - n) * (m + n + a) = 0 := by
      have eq1 : m^2 + a * m + 312 = 0 := hm2
      have eq2 : n^2 + a * n + 312 = 0 := hn2
      have eq3 : m^2 + a * m + 312 - (n^2 + a * n + 312) = 0 := by
        rw [eq1, eq2]
        all_goals norm_num
      have eq4 : m^2 + a * m + 312 - (n^2 + a * n + 312) = (m^2 - n^2) + (a * m - a * n) := by
        ring_nf
      rw [eq4] at eq3
      have eq5 : (m^2 - n^2) + (a * m - a * n) = (m - n) * (m + n + a) := by
        ring
      rw [eq5] at eq3
      linarith
    cases' (mul_eq_zero.1 h1) with h2 h3
    · -- m - n = 0, but m ≠ n, contradiction
      exfalso
      have : m = n := by
        linarith
      contradiction
    · -- m + n + a = 0, so a = -(m + n)
      have ha_eq : a = -(m + n) := by
        linarith
      have hmn : m * n = 312 := by
        rw [ha_eq] at hm2
        nlinarith
      by_contra h
      push_neg at h
      have ha2 : a ≥ -36 := by omega
      have h3 : m + n ≤ 36 := by
        nlinarith [ha_eq, ha2]
      have h4 : m ≤ 36 := by 
        nlinarith [show m ≤ m + n by nlinarith, h3, show n > 0 by linarith]
      have h5 : n ≤ 36 := by 
        nlinarith [show n ≤ m + n by nlinarith, h3, show m > 0 by linarith]
      interval_cases m <;> omega