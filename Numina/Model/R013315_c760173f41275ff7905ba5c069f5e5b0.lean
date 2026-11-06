import Mathlib

theorem algebra_189925 (a b c d e f g h k : ℤ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hg : g = 1 ∨ g = -1) (hh : h = 1 ∨ h = -1) (hk : k = 1 ∨ k = -1) :
    a * e * k - a * f * h + b * f * g - b * d * k + c * d * h - c * e * g ≤ 4 := by 
  rcases ha with ha1 | ha1
  all_goals rcases hb with hb1 | hb1
  all_goals rcases hc with hc1 | hc1
  all_goals rcases hd with hd1 | hd1
  all_goals rcases he with he1 | he1
  all_goals rcases hf with hf1 | hf1
  all_goals rcases hg with hg1 | hg1
  all_goals rcases hh with hh1 | hh1
  all_goals rcases hk with hk1 | hk1 
  all_goals 
    simp only [ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1, hk1]
    <;> omega