import Mathlib

theorem algebra_303791 (a b c : ℤ) :
    (∀ x : ℝ, (x - a) * (x - 2005) - 2 = (x - b) * (x - c)) ↔
    (a = 2004 ∧ b = 2003 ∧ c = 2006) ∨
    (a = 2004 ∧ b = 2006 ∧ c = 2003) ∨
    (a = 2006 ∧ b = 2004 ∧ c = 2007) ∨
    (a = 2006 ∧ b = 2007 ∧ c = 2004) := by
  constructor
  · -- Assume the equation holds for all real x, prove the possible triples.
    intro h
    have eq1 := h 0
    have eq2 := h 1
    ring_nf at eq1 eq2
    have eq3 : (a : ℝ) + 2005 = (b : ℝ) + (c : ℝ) := by
      nlinarith
    have eq4 : a + 2005 = b + c := by
      exact_mod_cast eq3
    have eq5 : (2005 : ℝ) * (a : ℝ) - 2 = (b : ℝ) * (c : ℝ) := by
      nlinarith
    have eq6 : 2005 * a - 2 = b * c := by
      exact_mod_cast eq5
    have eq7 : (b - 2005 : ℤ) * (b - a : ℤ) = 2 := by
      have eq8 : c = a + 2005 - b := by
        omega
      rw [eq8] at eq6
      nlinarith
    have h1 : (b - 2005) * (b - a) = 2 := eq7
    have h2 : (b - 2005) ∣ 2 := by
      use (b - a)
      linarith
    have h3 : (b - 2005) = 1 ∨ (b - 2005) = -1 ∨ (b - 2005) = 2 ∨ (b - 2005) = -2 := by 
      have h4 : (b - 2005) ∣ 2 := h2
      have h5 : (b - 2005) ≤ 2 := by 
        exact Int.le_of_dvd (by norm_num) h4
      have h6 : (b - 2005) ≥ -2 := by 
        have h7 : (- (b - 2005)) ∣ 2 := by 
          exact Int.neg_dvd.2 h4
        have h8 : - (b - 2005) ≤ 2 := by 
          exact Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases (b - 2005) <;> tauto
    rcases h3 with h4 | h5 | h6 | h7
    · -- Case b - 2005 = 1
      have h8 : b = 2006 := by linarith
      have h9 : a = 2004 := by
        have h10 : (b - a : ℤ) = 2 := by
          nlinarith [h1, h8]
        nlinarith
      have h10 : c = 2003 := by
        linarith [eq4, h8, h9]
      simp [h9, h8, h10]
    · -- Case b - 2005 = -1
      have h8 : b = 2004 := by linarith
      have h9 : a = 2006 := by
        have h10 : (b - a : ℤ) = -2 := by
          nlinarith [h1, h8]
        nlinarith
      have h10 : c = 2007 := by
        linarith [eq4, h8, h9]
      simp [h9, h8, h10]
    · -- Case b - 2005 = 2
      have h8 : b = 2007 := by linarith
      have h9 : a = 2006 := by
        have h10 : (b - a : ℤ) = 1 := by
          nlinarith [h1, h8]
        nlinarith
      have h10 : c = 2004 := by
        linarith [eq4, h8, h9]
      simp [h9, h8, h10]
    · -- Case b - 2005 = -2
      have h8 : b = 2003 := by linarith
      have h9 : a = 2004 := by
        have h10 : (b - a : ℤ) = -1 := by
          nlinarith [h1, h8]
        nlinarith
      have h10 : c = 2006 := by
        linarith [eq4, h8, h9]
      simp [h9, h8, h10]
  · -- Prove the reverse direction
    rintro (h | h | h | h)
    · -- Case 1
      rcases h with ⟨ha, hb, hc⟩
      intro x
      rw [show (a : ℝ) = (2004 : ℝ) by exact_mod_cast ha, 
          show (b : ℝ) = (2003 : ℝ) by exact_mod_cast hb, 
          show (c : ℝ) = (2006 : ℝ) by exact_mod_cast hc]
      ring
    · -- Case 2
      rcases h with ⟨ha, hb, hc⟩
      intro x
      rw [show (a : ℝ) = (2004 : ℝ) by exact_mod_cast ha, 
          show (b : ℝ) = (2006 : ℝ) by exact_mod_cast hb, 
          show (c : ℝ) = (2003 : ℝ) by exact_mod_cast hc]
      ring
    · -- Case 3
      rcases h with ⟨ha, hb, hc⟩
      intro x
      rw [show (a : ℝ) = (2006 : ℝ) by exact_mod_cast ha, 
          show (b : ℝ) = (2004 : ℝ) by exact_mod_cast hb, 
          show (c : ℝ) = (2007 : ℝ) by exact_mod_cast hc]
      ring
    · -- Case 4
      rcases h with ⟨ha, hb, hc⟩
      intro x
      rw [show (a : ℝ) = (2006 : ℝ) by exact_mod_cast ha, 
          show (b : ℝ) = (2007 : ℝ) by exact_mod_cast hb, 
          show (c : ℝ) = (2004 : ℝ) by exact_mod_cast hc]
      ring