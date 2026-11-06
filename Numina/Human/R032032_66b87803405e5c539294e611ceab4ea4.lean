import Mathlib

open Set

/- If the equation $x^{2}-(m+1)x+4=0$ has two distinct real roots in the interval $(0,3]$, determine the range of values for $m$.\n\nA: $(3, \\frac {10}{3})$\nB: $[3, \\frac {10}{3})$\nC: $[3, \\frac {10}{3}]$\nD: $(3, \\frac {10}{3}]$ -/
theorem algebra_525610 :
    {m : ℝ | ∃ x y, x ≠ y ∧ x ∈ Ioc 0 3 ∧ y ∈ Ioc 0 3 ∧
    x^2 - (m + 1)*x + 4 = 0 ∧ y^2 - (m + 1)*y + 4 = 0} = Set.Ioc 3 (10/3) := by
  ext m
  simp
  constructor
  . rintro ⟨x, y, hxy, ⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩, fx, fy⟩
    rw [lt_iff_le_and_ne]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    . have h₁ : m + 1 > 0 := by
        replace fx : m + 1 = (x ^ 2 + 4) / x := by
          field_simp
          linarith only [fx]
        rw [fx]
        positivity
      replace fx : (2 * x - (m + 1)) ^ 2 = (m - 3) * (m + 5) := by linarith only [fx]
      replace fx : 0 ≤ (m - 3) * (m + 5) := by
        rw [← fx]
        positivity
      nlinarith only [h₁, fx]
    . rintro rfl
      replace fx : (x - 2) ^ 2 = 0 := by linarith only [fx]
      replace fy : (y - 2) ^ 2 = 0 := by linarith only [fy]
      simp [sub_eq_zero] at fx fy
      simp [fx, fy] at hxy
    . by_contra! h
      have h₁ : 0 < (3 - x) * (m - 2 - x) := by linarith only [fx, h]
      have h₂ : 0 < m - 2 - x := pos_of_mul_pos_right h₁ (by linarith only [hx₂])
      have h₃ : (x - y) * (x + y - (m + 1)) = 0 := by linarith only [fx, fy]
      simp [sub_eq_zero, hxy] at h₃
      linarith only [hy₂, h₂, h₃]
  . rintro ⟨hm₁, hm₂⟩
    let f x := x ^ 2 - (m + 1) * x + 4
    have h₁ : f 0 > 0 := by simp [f]
    have h₂ : f ((m + 1) / 2) < 0 := by
      simp [f]
      nlinarith
    have h₃ : f 3 ≥ 0 := by
      simp [f]
      linarith only [hm₂]
    have h₄ : 0 ≤ (m + 1) / 2 := by linarith only [hm₁]
    have h₅ : (m + 1) / 2 ≤ 3 := by linarith only [hm₂]
    have hfcont : Continuous f := by continuity
    have h₆ : 0 ∈ Ioo (f ((m + 1) / 2)) (f 0) := by
      simp [h₂, h₁]
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' h₄ (Continuous.continuousOn hfcont) h₆
    have h₇ : 0 ∈ Ioc (f ((m + 1) / 2)) (f 3) := by
      simp [h₂, h₃]
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Ioc h₅ (Continuous.continuousOn hfcont) h₇
    use x, y
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hfx, hfy⟩
    all_goals
      simp at hx hy
      linarith only [hx, hy]
