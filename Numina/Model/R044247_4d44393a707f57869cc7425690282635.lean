import Mathlib

theorem number_theory_287636 (A B : ℕ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A ≠ B) (hA1 : A < 1000) (hB1 : B < 1000) :
    (A - B : ℝ) / (A + B) ≤ 499 / 500 := by
  have h1 : A ≤ 999 := by linarith
  have h2 : B ≤ 999 := by linarith
  have h3 : (A : ℝ) ≤ (999 : ℝ) := by exact_mod_cast h1
  have h4 : (B : ℝ) ≤ (999 : ℝ) := by exact_mod_cast h2
  have h5 : (A : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ A from by
    by_contra h
    push_neg at h
    have h6 : A = 0 := by linarith
    contradiction
  )
  have h6 : (B : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ B from by
    by_contra h
    push_neg at h
    have h7 : B = 0 := by linarith
    contradiction
  )
  have h7 : (A : ℝ) ≤ 999 * (B : ℝ) := by
    have ha : (A : ℝ) ≤ 999 := by exact_mod_cast (show A ≤ 999 by linarith)
    have hb : (B : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ B by 
      by_contra h
      push_neg at h
      have h7 : B = 0 := by linarith
      contradiction
    )
    nlinarith
  have h8 : (A + B : ℝ) > 0 := by
    have ha : (A : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ A by
      by_contra h
      push_neg at h
      have h6 : A = 0 := by linarith
      contradiction
    )
    have hb : (B : ℝ) ≥ 1 := by exact_mod_cast (show 1 ≤ B by
      by_contra h
      push_neg at h
      have h7 : B = 0 := by linarith
      contradiction
    )
    linarith
  have h9 : (A - B : ℝ) / (A + B) ≤ 499 / 500 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h7]
  exact h9