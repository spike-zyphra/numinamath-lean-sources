import Mathlib

theorem algebra_11953 (a b c d e f : ℝ)
    (ha : 0 < a ∧ a = 6) (hb : 0 < b ∧ b = 8)
    (hc : 0 < c ∧ c = 32) (hd : 0 < d ∧ d = 24)
    (he : 0 < e ∧ e = 13) (hf : 0 < f ∧ f = 5)
    (h : (1/2) * e * f = (1/4) * a * b) :
    e * f = 4 * Real.sqrt 3 := by
  rcases ha with ⟨ha_pos, ha_eq⟩
  rcases hb with ⟨hb_pos, hb_eq⟩
  rcases he with ⟨he_pos, he_eq⟩
  rcases hf with ⟨hf_pos, hf_eq⟩
  rw [ha_eq, hb_eq, he_eq, hf_eq] at h
  norm_num at h
  all_goals nlinarith