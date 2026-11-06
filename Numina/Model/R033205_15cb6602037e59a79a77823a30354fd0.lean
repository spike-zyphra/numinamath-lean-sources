import Mathlib

theorem algebra_216265 (a b c d e f g h k : ℤ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hg : g = 1 ∨ g = -1) (hh : h = 1 ∨ h = -1) (hk : k = 1 ∨ k = -1) :
    a * e * k - a * f * h + b * f * g - b * d * k + c * d * h - c * e * g ≤ 4 := by 
  rcases ha with (rfl | rfl)
  <;> rcases hb with (rfl | rfl)
  <;> rcases hc with (rfl | rfl)
  <;> rcases hd with (rfl | rfl)
  <;> rcases he with (rfl | rfl)
  <;> rcases hf with (rfl | rfl)
  <;> rcases hg with (rfl | rfl)
  <;> rcases hh with (rfl | rfl)
  <;> rcases hk with (rfl | rfl)
  <;> omega