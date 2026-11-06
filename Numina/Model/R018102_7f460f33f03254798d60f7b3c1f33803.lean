import Mathlib

theorem algebra_654 (x : ℝ) (hx : x = 3 / 8 + 2 / 5) (a b c : ℕ) (h01 : 0 ≤ a ∧ a ≤ 9) (h1 : 0 ≤ b ∧ b ≤ 9) (h2 : 0 ≤ c ∧ c ≤ 9) (h : x = (a * 100 + b * 10 + 2) / 100 + (c * 10 + 5) / 10) : a + b + c = 3 := by
  rcases h01 with ⟨ha0, ha1⟩
  rcases h1 with ⟨hb0, hb1⟩
  rcases h2 with ⟨hc0, hc1⟩
  norm_num [hx] at h
  have h31 : a ≤ 9 := by linarith
  have h32 : b ≤ 9 := by linarith
  have h33 : c ≤ 9 := by linarith
  have h_eq6 : (a * 100 + b * 10 + 2 : ℝ) + ((c * 10 + 5 : ℝ) * 10) = (31 / 40 : ℝ) * 100 := by
    linarith [h]
  have h_eq9 : (200 * (a : ℝ) + 200 * (c : ℝ) + 20 * (b : ℝ) = 51) := by
    norm_num at h_eq6
    linarith [h_eq6]
  have h_eq11 : 200 * (a : ℤ) + 200 * (c : ℤ) + 20 * (b : ℤ) = 51 := by 
    exact_mod_cast h_eq9
  omega