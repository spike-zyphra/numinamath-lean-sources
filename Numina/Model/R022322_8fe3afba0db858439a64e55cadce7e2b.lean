import Mathlib

theorem algebra_303872 :
    IsGreatest {x | ∃ a b c d e f g h k : ℤ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧ (c = 1 ∨ c = -1) ∧
      (d = 1 ∨ d = -1) ∧ (e = 1 ∨ e = -1) ∧ (f = 1 ∨ f = -1) ∧ (g = 1 ∨ g = -1) ∧ (h = 1 ∨ h = -1) ∧
      (k = 1 ∨ k = -1) ∧ x = a * e * k - a * f * h + b * f * g - b * d * k + c * d * h - c * e * g} 4 := by
  constructor
  · -- Show 4 is feasible
    use 1, 1, 1, 1, -1, 1, 1, 1, -1
    norm_num
    all_goals norm_num
  · -- Show 4 is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, d, e, f, g, h, k, ha, hb, hc, hd, he, hf, hg, hh, hk, hx⟩
    have ha1 : a = 1 ∨ a = -1 := ha
    have hb1 : b = 1 ∨ b = -1 := hb
    have hc1 : c = 1 ∨ c = -1 := hc
    have hd1 : d = 1 ∨ d = -1 := hd
    have he1 : e = 1 ∨ e = -1 := he
    have hf1 : f = 1 ∨ f = -1 := hf
    have hg1 : g = 1 ∨ g = -1 := hg
    have hh1 : h = 1 ∨ h = -1 := hh
    have hk1 : k = 1 ∨ k = -1 := hk
    have h1 : a * e * k - a * f * h + b * f * g - b * d * k + c * d * h - c * e * g ≤ 4 := by
      have ha2 : a = 1 ∨ a = -1 := ha
      have hb1 : b = 1 ∨ b = -1 := hb
      have hc1 : c = 1 ∨ c = -1 := hc
      have hd1 : d = 1 ∨ d = -1 := hd
      have he1 : e = 1 ∨ e = -1 := he
      have hf1 : f = 1 ∨ f = -1 := hf
      have hg1 : g = 1 ∨ g = -1 := hg
      have hh1 : h = 1 ∨ h = -1 := hh
      have hk1 : k = 1 ∨ k = -1 := hk
      rcases ha2 with (rfl | rfl)
      <;> rcases hb1 with (rfl | rfl)
      <;> rcases hc1 with (rfl | rfl)
      <;> rcases hd1 with (rfl | rfl)
      <;> rcases he1 with (rfl | rfl)
      <;> rcases hf1 with (rfl | rfl)
      <;> rcases hg1 with (rfl | rfl)
      <;> rcases hh1 with (rfl | rfl)
      <;> rcases hk1 with (rfl | rfl)
      <;> omega
    linarith