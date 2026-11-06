import Mathlib

theorem number_theory_18713 :
    IsLeast {x | ∃ a b n m : ℕ, a > 0 ∧ b > 0 ∧ n = a * (1 + 30 / 100 : ℝ) ∧ m = b * (1 - 20 / 100 : ℝ) ∧ x = n * m} 52 := by
  constructor
  · -- Show 52 is in the set
    use 10, 5, 13, 4
    norm_num
  · -- Show 52 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, n, m, ha, hb, hn, hm, hx⟩
    have hn' : (n : ℝ) = (a : ℝ) * (1 + 30 / 100 : ℝ) := by
      linarith [hn]
    have hm' : (m : ℝ) = (b : ℝ) * (1 - 20 / 100 : ℝ) := by
      linarith [hm]
    have eq1 : (n : ℝ) = (a : ℝ) * (13 / 10 : ℝ) := by
      rw [hn']
      norm_num
    have eq2 : (m : ℝ) = (b : ℝ) * (4 / 5 : ℝ) := by
      rw [hm']
      norm_num
    have h1 : (10 * (n : ℝ) = (13 * (a : ℝ))) := by
      have h2 : (n : ℝ) = (a : ℝ) * (13 / 10 : ℝ) := eq1
      linarith
    have h2 : (5 * (m : ℝ) = (4 * (b : ℝ))) := by
      have h3 : (m : ℝ) = (b : ℝ) * (4 / 5 : ℝ) := eq2
      linarith
    have eq3 : 10 * n = 13 * a := by
      exact_mod_cast h1
    have eq4 : 5 * m = 4 * b := by
      exact_mod_cast h2
    have h3 : n % 13 = 0 := by
      omega
    have h4 : m % 4 = 0 := by
      omega
    have hn1 : n ≥ 13 := by
      omega
    have hm1 : m ≥ 4 := by
      omega
    have h5 : n * m ≥ 52 := by
      nlinarith
    nlinarith [hx, h5]