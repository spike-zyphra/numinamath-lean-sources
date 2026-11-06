import Mathlib

open Real
open scoped BigOperators

theorem inequalities_6935 :
  Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ 100 ∧ p.2 ≤ 100 ∧ 0 < (p.1 + p.2 : ℝ) / (p.1 - p.2) ∧ (p.1 + p.2 : ℝ) / (p.1 - p.2) < 2} = 1617 := by
  have h2 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ 100 ∧ p.2 ≤ 100 ∧ 0 < (p.1 + p.2 : ℝ) / (p.1 - p.2) ∧ (p.1 + p.2 : ℝ) / (p.1 - p.2) < 2} = Finset.filter (fun (p : ℕ × ℕ) => p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ 100 ∧ p.2 ≤ 100 ∧ (p.1 > p.2) ∧ (p.1 > 3 * p.2)) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume (0 < (m + n) / (m - n) ∧ (m + n : ℝ) / (m - n) < 2)
      rintro ⟨h1, h2, h3, h4, h5, h6⟩
      have h7 : m > n := by
        by_contra h
        push_neg at h
        have h8 : m ≤ n := by
          omega
        have h9 : (m : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast h8
        have h10 : (m + n : ℝ) / (m - n : ℝ) ≤ 0 := by
          have h11 : (m - n : ℝ) ≤ 0 := by
            nlinarith
          have h12 : (m + n : ℝ) ≥ 0 := by
            positivity
          apply div_nonpos_of_nonneg_of_nonpos
          all_goals
            nlinarith
        nlinarith
      have h8 : m > 3 * n := by
        by_contra h
        push_neg at h
        have h9 : m ≤ 3 * n := by
          omega
        have h10 : (m : ℝ) ≤ (3 * (n : ℝ)) := by
          exact_mod_cast h9
        have h11 : (m + n : ℝ) / (m - n : ℝ) ≥ (2 : ℝ) := by
          have h12 : (m : ℝ) ≤ (3 * (n : ℝ)) := by
            nlinarith
          have h13 : (m - n : ℝ) > 0 := by
            have hn : (m : ℝ) > (n : ℝ) := by
              exact_mod_cast (show m > n by linarith)
            nlinarith
          have h14 : (m + n : ℝ) ≥ (2 : ℝ) * (m - n : ℝ) := by
            nlinarith [h12]
          have h15 : (m + n : ℝ) / (m - n : ℝ) ≥ (2 : ℝ) := by
            apply (le_div_iff₀ (by positivity)).mpr
            linarith
          nlinarith
        nlinarith
      tauto
    · -- Assume (n < m ∧ m > 3 * n)
      rintro ⟨h1, h2, h3, h4, h5, h6⟩
      constructor
      · -- Show m > 0
        omega
      constructor
      · -- Show n > 0
        omega
      constructor
      · -- Show m ≤ 100
        omega
      constructor
      · -- Show n ≤ 100
        omega
      constructor
      · -- Show 0 < (m + n) / (m - n)
        have h5' : (m : ℝ) > (n : ℝ) := by
          exact_mod_cast (show (m : ℕ) > (n : ℕ) by omega)
        have h3n' : (m : ℝ) > (3 * (n : ℝ)) := by
          have h : (m : ℝ) > (3 * (n : ℝ)) := by
            have h5'' : (m > 3 * n) := by
              omega
            norm_cast at *
          linarith
        have h_pos : (m - n : ℝ) > 0 := by
          nlinarith
        have h : (m + n : ℝ) > 0 := by
          positivity
        have h2_pos : ((m + n : ℝ) / (m - n : ℝ)) > (0 : ℝ) := by
          apply div_pos
          all_goals
            positivity
        norm_cast at *
      · -- Show (m + n) / (m - n) < 2
        have h5' : (m : ℝ) > (n : ℝ) := by
          exact_mod_cast (show (m : ℕ) > (n : ℕ) by omega)
        have h3n' : (m : ℝ) > (3 * (n : ℝ)) := by
          have h : (m : ℝ) > (3 * (n : ℝ)) := by
            have h5'' : (m > 3 * n) := by
              omega
            norm_cast at *
          linarith
        have h_pos : (m - n : ℝ) > 0 := by
          nlinarith
        have h2_lt : ((m + n : ℝ) / (m - n : ℝ)) < (2 : ℝ) := by
          have h13 : (m + n : ℝ) < (2 : ℝ) * (m - n : ℝ) := by
            have h6' : m > 3 * n := by
              omega
            have h7' : (m : ℝ) > (3 * (n : ℝ)) := by
              exact_mod_cast h6'
            nlinarith
          apply (div_lt_iff₀ (by positivity)).mpr
          linarith
        norm_cast at *
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide