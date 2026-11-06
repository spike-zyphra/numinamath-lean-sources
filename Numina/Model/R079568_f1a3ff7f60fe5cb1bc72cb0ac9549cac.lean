import Mathlib

theorem algebra_270150 {a b c : ℤ} (ha : 5 ∣ a) (hb : 5 ∣ b) (hc : 5 ∣ c)
    (hord : a < b ∧ b < c) (hc1 : c = a + 10) :
    (a - b) * (a - c) / (b - c) = -10 := by
  rcases ha with ⟨k, h1⟩
  rcases hb with ⟨l, h2⟩
  rcases hc with ⟨m, h3⟩
  have h_eq : 5 * m = 5 * k + 10 := by
    linarith [hc1, h1, h3]
  have hm : m = k + 2 := by
    linarith
  have h4 : k < l := by
    nlinarith [hord.1, h1, h2]
  have h5 : l < m := by
    nlinarith [hord.2, h2, h3]
  have hl : l = k + 1 := by
    rw [hm] at h5
    omega
  have ha_b : a - b = -5 := by
    rw [h1, h2]
    rw [hl]
    linarith
  have ha_c : a - c = -10 := by
    rw [h1, h3]
    rw [hm]
    linarith
  have hb_c : b - c = -5 := by
    rw [h2, h3]
    rw [hl, hm]
    linarith
  -- Now compute the entire expression
  rw [ha_b, ha_c, hb_c]
  norm_num
  all_goals omega