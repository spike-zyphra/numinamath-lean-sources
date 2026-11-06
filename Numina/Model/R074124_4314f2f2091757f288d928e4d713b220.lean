import Mathlib

theorem algebra_10964 (total_counties : ℕ) (h : total_counties ≠ 0)
    (h1 : (59 / 100 : ℝ) * total_counties + (25 / 100 : ℝ) * total_counties + (16 / 100 : ℝ) * total_counties = total_counties) :
    (84 / 100 : ℝ) * total_counties = total_counties - (16 / 100 : ℝ) * total_counties := by
  have eq1 : (total_counties : ℝ) > 0 := by
    have h3 : total_counties > 0 := by
      by_contra h4
      push_neg at h4
      have h5 : total_counties = 0 := by
        omega
      contradiction
    exact_mod_cast h3
  ring_nf at h1 ⊢
  <;> linarith