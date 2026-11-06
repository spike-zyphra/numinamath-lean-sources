import Mathlib

theorem algebra_20301_mod (a b c : ℝ) (n : ℕ)
  (hpos_a : 0 < a) (hpos_b : 0 < b) (hpos_c : 0 < c)
  (h₀ : 1 * a = 4 * b) (h₁ : 3 * b = 7 * c)
  (h₂ : 56 * c = n * a) :
  n = 6 := by
  have ha : a = 4 * b := by
    linarith
  have hb : b = 7 / 3 * c := by
    linarith
  have ha' : a = 28 / 3 * c := by 
    rw [hb] at ha
    linarith
  have h3 : 56 * c = (n : ℝ) * a := by 
    exact_mod_cast h₂
  rw [ha'] at h3
  have h4 : 56 * c = (n : ℝ) * (28 / 3 * c) := by
    linarith
  have h5 : 56 = (n : ℝ) * (28 / 3) := by
    have hc : 0 < c := hpos_c
    apply (mul_left_inj' (ne_of_gt hc)).mp
    linarith
  have hn : (n : ℝ) = 6 := by 
    linarith
  have hn_nat : n = 6 := by
    exact_mod_cast hn
  exact hn_nat