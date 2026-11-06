import Mathlib
open Nat

/-Farmer James has some strange animals. His hens have 2 heads and 8 legs, his peacocks have 3 heads and 9 legs, and his zombie hens have 6 heads and 12 legs. Farmer James counts 800 heads and 2018 legs on his farm. What is the number of animals that Farmer James has on his farm? -/
theorem logic_and_puzzles_612345 (hens peacocks zombie_hens : ℕ)
    (h_heads : 2 * hens + 3 * peacocks + 6 * zombie_hens = 800)
    (h_legs : 8 * hens + 9 * peacocks + 12 * zombie_hens = 2018) :
    hens + peacocks + zombie_hens = 203 := by
  -- Note that each animal has $6$ more legs than heads.
  have h_hen_diff : 8 - 2 = 6 := by norm_num
  have h_peacock_diff : 9 - 3 = 6 := by norm_num
  have h_zombie_diff : 12 - 6 = 6 := by norm_num
  -- There are $2018-800=1218$ more legs than heads in total.
  have h_legs_minus_heads : (8 * hens + 9 * peacocks + 12 * zombie_hens) - (2 * hens + 3 * peacocks + 6 * zombie_hens) = 2018 - 800 := by
    rw [h_legs, h_heads]
  have h_diff_value : 2018 - 800 = 1218 := by norm_num
  -- So there are $\frac{1218}{6}=203$ animals.
  have h_diff_simplify : (8 * hens + 9 * peacocks + 12 * zombie_hens) - (2 * hens + 3 * peacocks + 6 * zombie_hens) = 6 * (hens + peacocks + zombie_hens) := by
    calc
      (8 * hens + 9 * peacocks + 12 * zombie_hens) - (2 * hens + 3 * peacocks + 6 * zombie_hens)
      = (8 * hens - 2 * hens) + (9 * peacocks - 3 * peacocks) + (12 * zombie_hens - 6 * zombie_hens) := by omega
      _ = 6 * hens + 6 * peacocks + 6 * zombie_hens := by omega
      _ = 6 * (hens + peacocks + zombie_hens) := by ring
  have h_eq_6n : 6 * (hens + peacocks + zombie_hens) = 1218 := by
    rw [← h_diff_simplify, h_legs_minus_heads, h_diff_value]
  have h_n_eq_203 : hens + peacocks + zombie_hens = 1218 / 6 := by
    norm_num [Nat.div_eq_of_eq_mul_left (show 0 < 6 by norm_num)]
    linarith
  have h_div_result : 1218 / 6 = 203 := by norm_num
  have h_final : hens + peacocks + zombie_hens = 203 := by
    rw [h_n_eq_203, h_div_result]
  exact h_final