import Mathlib

theorem algebra_97389 (u : ℕ → ℝ) (h₀ : ∀ n, u (n + 2) = 2 * u (n + 1) + u n)
    (h₁ : u 3 = 9) (h₂ : u 6 = 128) : u 5 = 53 := by 
  have eq3 : u 5 = 2 * u 4 + u 3 := by
    specialize h₀ 3
    norm_num at h₀ ⊢
    linarith

  have eq4 : u 6 = 2 * u 5 + u 4 := by
    specialize h₀ 4
    norm_num at h₀ ⊢
    linarith

  rw [h₁] at eq3 -- substituting u 3 = 9 into eq3
  rw [h₂] at eq4 -- substituting u 6 = 128 into eq4

  -- Solving the linear system:
  -- From eq3: u 5 = 2 * u 4 + 9
  -- From eq4: 128 = 2 * u 5 + u 4
  linarith [eq3, eq4] -- solving the system of equations using linear arithmetic