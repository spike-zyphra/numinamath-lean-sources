import Mathlib

theorem algebra_207607 (a b c : ℝ) (ha : 0 < a ∧ a = 1 / 6) (hb : 0 < b ∧ b = 1 / 8)
    (hc : 0 < c ∧ c = 1 / 3) :
    30 / (5 * a + 3 * b + 2 * c) = 16 := by
  rcases ha with ⟨ha_pos, ha_eq⟩
  rcases hb with ⟨hb_pos, hb_eq⟩
  rcases hc with ⟨hc_pos, hc_eq⟩

  have h1 : 5 * a + 3 * b + 2 * c = 15 / 8 := by
    rw [ha_eq, hb_eq, hc_eq]
    norm_num
  rw [h1]
  norm_num