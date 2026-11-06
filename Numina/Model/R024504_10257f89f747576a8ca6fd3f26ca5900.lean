import Mathlib

theorem number_theory_279690 : ¬∃ (r : ℚ), Real.sqrt 13 = r := by
  -- Assume for contradiction that there exists a rational r such that Real.sqrt 13 = r
  rintro ⟨r, hr⟩
  -- Show that Real.sqrt 13 is irrational
  have h1 : Irrational (Real.sqrt 13) := by
    native_decide
  -- Show that Real.sqrt 13 being equal to a rational is a contradiction
  have h2 : ¬Irrational (Real.sqrt 13) := by
    rw [show Real.sqrt 13 = (r : ℝ) by exact_mod_cast hr]
    simp
  -- Contradiction between h1 and h2
  contradiction