import Mathlib

theorem number_theory_165209 : ¬∃ q : ℚ, Real.sqrt 2 = q := by
  intro h
  rcases h with ⟨q, hq⟩
  have h1 : Irrational (Real.sqrt 2) := by
    apply irrational_sqrt_two
  rw [hq] at h1
  simp at h1