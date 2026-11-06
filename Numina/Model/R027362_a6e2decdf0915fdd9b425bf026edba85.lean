import Mathlib

theorem number_theory_168799 (x : ℚ) (h : ∃ y : ℚ, x * Real.sqrt 2 = y) : x = 0 := by
  rcases h with ⟨y, hy⟩
  by_contra hx
  have hx2 : (x : ℝ) ≠ 0 := by
    exact_mod_cast hx
  have h1 : Real.sqrt 2 = (y / (x : ℝ)) := by
    have h2 : (x : ℝ) * Real.sqrt 2 = (y : ℝ) := by
      simpa using hy
    have h3 : (x : ℝ) ≠ 0 := hx2
    field_simp
    linarith
  have h2 : ¬ Irrational (Real.sqrt 2) := by
    rw [h1]
    simp [hx2]
    <;> ring_nf <;> norm_num
  have h4 : Irrational (Real.sqrt 2) := by
    apply irrational_sqrt_two
  contradiction