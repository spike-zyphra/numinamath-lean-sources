import Mathlib

open Finset

theorem number_theory_122007 (L : ℕ) :
    ∃ x y : ℤ, x > 0 ∧ y > 0 ∧
      ∀ x' y' : ℤ, x' ∈ Icc x (x + L - 1) ∧ y' ∈ Icc y (y + L - 1) →
        ∃ x'' y'' : ℤ, x'' > 0 ∧ y'' > 0 ∧
          (x' : ℝ) / x'' = (y' : ℝ) / y'' := by 
  use 2 
  use 2 
  constructor 
  · norm_num
  constructor 
  · norm_num
  intro x' y' h 
  rcases h with ⟨hx, hy⟩ 
  rw [mem_Icc] at hx hy
  use x'
  use y'
  constructor 
  · 
    omega 
  constructor 
  · 
    omega 
  · 
    -- Show that x' / x'' = (y' / y'')
    have hx2 : (x' : ℝ) ≠ 0 := by 
      have hx1 : x' > 0 := by 
        omega 
      have hx3 : x' > (0 : ℝ) := by 
        exact_mod_cast hx1 
      linarith 
    have hy2 : (y' : ℝ) ≠ 0 := by 
      have hy1 : y' > 0 := by 
        omega 
      have hy3 : y' > (0 : ℝ) := by 
        exact_mod_cast hy1 
      linarith 
    field_simp [hx2, hy2]