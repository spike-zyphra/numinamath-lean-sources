import Mathlib

theorem algebra_3322 (a b c : ℤ) (h₁ : a ≠ 0) (h₂ : a + b + c = -2) (h₃ : 4*a + 2*b + c = 5)
    (h₄ : 9*a + 3*b + c = 14) :
    IsLeast {x | ∃ t : ℝ, x = a*t^2 + b*t + c} (-11) := by

  have eq4 : (a : ℝ) + (b : ℝ) + (c : ℝ) = -2 := by exact_mod_cast h₂
  have eq5 : (4 : ℝ) * (a : ℝ) + (2 : ℝ) * (b : ℝ) + (c : ℝ) = (5 : ℝ) := by exact_mod_cast h₃
  have eq6 : (9 : ℝ) * (a : ℝ) + (3 : ℝ) * (b : ℝ) + (c : ℝ) = (14 : ℝ) := by exact_mod_cast h₄

  have ha : (a : ℝ) = 1 := by
    nlinarith
  have hb : (b : ℝ) = 4 := by
    nlinarith

  have hc : (c : ℝ) = -7 := by
    nlinarith

  constructor
  · -- Prove that -11 is in the set
    use (-2 : ℝ)
    rw [show (a : ℝ) = 1 by exact_mod_cast ha]
    rw [show (b : ℝ) = 4 by exact_mod_cast hb]
    rw [show (c : ℝ) = -7 by exact_mod_cast hc]
    norm_num
  · -- Prove that -11 is the least in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [show (a : ℝ) = 1 by exact_mod_cast ha] at ht
    rw [show (b : ℝ) = 4 by exact_mod_cast hb] at ht
    rw [show (c : ℝ) = -7 by exact_mod_cast hc] at ht
    have h : (t + 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith