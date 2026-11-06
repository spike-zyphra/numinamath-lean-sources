import Mathlib

/- 8.2. How many solutions does the equation $(2 x+y)^{2}=2017+x^{2}$ have in integers $x, y$?-/
theorem number_theory_162499 : {(x, y) : ℤ × ℤ | (2 * x + y) ^ 2 = 2017 + x ^ 2}.encard = 4 := by
  -- It suffices to show that the only solutions are (1008, -1007), (-1008, 3025), (-1008, 1007), (1008, 3025).
  suffices {(x, y) : ℤ × ℤ | (2 * x + y) ^ 2 = 2017 + x ^ 2} = {(1008, -1007), (-1008, 3025), (-1008, 1007), (1008, -3025)} by
    rw [this]
    simp [Set.encard]
  -- Break the goal into two parts.
  ext ⟨x, y⟩
  simp
  constructor
  . -- Show that if (2x + y)² = 2017 + x² then (x, y) is one of the four solutions.
    intro h₀
    -- It is equivalent to 2017 = (3x + y)(x + y).
    replace h₀ : 2017 = (3 * x + y) * (y + x) := by
      linarith
    -- Note that 2017 is a prime, so it is easy to divide the cases.
    have h₁ : Prime ((3 * x + y) * (y + x)) := by
      simp [<-h₀]
      native_decide
    rw [prime_mul_iff] at h₁
    obtain (⟨_, h₁⟩ | ⟨h₁, _⟩) := h₁
    . apply Int.isUnit_eq_one_or at h₁
      obtain h₁ | h₁ := h₁
      . -- The case that y + x = 1.
        simp [h₁] at h₀
        -- Solve to get x = 1008 and y = -1007.
        left
        omega
      . -- The case that y + x = -1.
        simp [h₁] at h₀
        -- Solve to get x = -1008 and y = 1007.
        right
        right
        left
        omega
    . apply Int.isUnit_eq_one_or at h₁
      obtain h₁ | h₁ := h₁
      . -- The cases that 3x + y = 1.
        simp [h₁] at h₀
        -- Solve to get x = -1008 and y = 3025.
        right
        left
        omega
      . -- The case that 3x + y = -1.
        simp [h₁] at h₀
        -- Solve to get x = 1008 and y = -3025.
        iterate 3 right
        omega
  . -- Show that the four solutions are indeed valid.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    <;> norm_num