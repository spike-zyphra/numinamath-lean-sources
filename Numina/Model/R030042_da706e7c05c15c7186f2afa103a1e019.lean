import Mathlib
theorem number_theory_609726 (x : ℚ) : (∃ r : ℚ, x * √2 = r) ↔ x = 0:= by
  constructor
  · -- Assume there exists rational r such that x * √2 = r, prove x = 0
    rintro ⟨r, hr⟩
    by_contra hx
    have h1 : x ≠ 0 := by
      exact hx
    have h2 : (x : ℝ) ≠ 0 := by
      exact_mod_cast h1
    have h3 : Irrational (√2) := by
      native_decide
    have h4 : ¬ Irrational (x * √2) := by
      rw [show x * √2 = (r : ℝ) by linarith [hr]]
      simp
    have h5 : Irrational (x * √2) := by
      have h6 : Irrational (√2) := h3
      have h7 : (x : ℝ) ≠ 0 := h2
      have h8 : Irrational (x * √2) := by
        have h9 : (x * √2 : ℝ) = ((x : ℚ) * (√2 : ℝ)) := by
          simp
        rw [h9]
        apply Irrational.rat_mul
        · exact h6
        · -- Show that x is non-zero rational
          exact_mod_cast h1
      exact h8
    contradiction
  · -- Assume x = 0, prove ∃ r : ℚ, x * √2 = r
    intro h
    rw [h]
    use (0 : ℚ)
    simp