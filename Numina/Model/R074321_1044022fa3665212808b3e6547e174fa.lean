import Mathlib

theorem algebra_192260 {a b c d : ℕ} (ha : a = ∑ i ∈ Finset.range 12, (3 * i + 5)) (hb : b = (Nat.digits 10 a).sum)
    (hc : c = b ^ 2) (hd : 3 * d = c) : d = 75 := by
  have ha2 : a = 258 := by 
    rw [ha]
    norm_num [Finset.sum_range_succ]
  have hb2 : b = 15 := by
    rw [hb, ha2]
    norm_num
  have hc2 : c = 225 := by 
    rw [hc, hb2]
    all_goals norm_num
  have hd2 : 3 * d = 225 := by 
    rw [hc2] at hd
    exact_mod_cast hd
  have : d = 75 := by 
    omega
  exact_mod_cast this