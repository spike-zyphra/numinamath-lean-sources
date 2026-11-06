import Mathlib

theorem number_theory_162069 (a b : ℤ) :
    (3 * a + 5 * b = 1 ↔ ∃ k, (a, b) = (2 - 5 * k, -1 + 3 * k)) ∧
    (3 * a + 5 * b = 4 ↔ ∃ k, (a, b) = (8 - 5 * k, -4 + 3 * k)) ∧
    (183 * a + 117 * b = 3 ↔ ∃ k, (a, b) = (16 - 39 * k, -25 + 61 * k)) := by
  constructor
  · -- Forward and Backward proof for the first equation
    constructor
    · -- Forward implication: If $(a, b)$ satisfies $3a + 5b = 1$, then it is of the form $(2 - 5k, -1 + 3k)$ for some integer $k$
      intro h
      use (2 - a) / 5
      have h1 : b = (-1 + 3 * ((2 - a) / 5)) := by
        omega
      simp [Prod.ext_iff, h1]
      all_goals omega
    · -- Backward implication: If $(a, b)$ is of the form $(2 - 5k, -1 + 3k)$, then it satisfies $3a + 5b = 1$
      rintro ⟨k, hk⟩
      rcases hk with ⟨rfl, rfl⟩
      ring
  constructor
  · -- Forward and Backward proof for the second equation
    constructor
    · -- Forward implication: If $(a, b)$ satisfies $3a + 5b = 4$, then it is of the form $(8 - 5k, -4 + 3k)$ for some integer $k$
      intro h
      use (8 - a) / 5
      have h1 : b = (-4 + 3 * ((8 - a) / 5)) := by
        omega
      simp [Prod.ext_iff, h1]
      all_goals omega
    · -- Backward implication: If $(a, b)$ is of the form $(8 - 5k, -4 + 3k)$, then it satisfies $3a + 5b = 4$
      rintro ⟨k, hk⟩
      rcases hk with ⟨rfl, rfl⟩
      ring
  · -- Forward and Backward proof for the third equation
    constructor
    · -- Forward implication: If $(a, b)$ satisfies $183a + 117b = 3$, then it is of the form $(16 - 39k, -25 + 61k)$ for some integer $k$
      intro h
      use (16 - a) / 39
      have h1 : b = (-25 + 61 * ((16 - a) / 39)) := by
        omega
      simp [Prod.ext_iff, h1]
      all_goals omega
    · -- Backward implication: If $(a, b)$ is of the form $(16 - 39k, -25 + 61k)$, then it satisfies $183a + 117b = 3$
      rintro ⟨k, hk⟩
      rcases hk with ⟨rfl, rfl⟩
      ring