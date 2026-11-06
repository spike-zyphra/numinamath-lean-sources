import Mathlib

open Real

theorem algebra_326646 {p : ℕ → ℝ} (hp0 : p 0 = 0) (hp1 : p 10 = 1)
    (hpn : ∀ n ∈ Finset.Ioo 0 10, p n = p (n - 1) * (n / 10) + p (n + 1) * (10 - n) / 10) :
    p 1 = 63 / 146 := by
  have eq1 := hpn 1 (by norm_num [Finset.mem_Ioo])
  have eq2 := hpn 2 (by norm_num [Finset.mem_Ioo])
  have eq3 := hpn 3 (by norm_num [Finset.mem_Ioo])
  have eq4 := hpn 4 (by norm_num [Finset.mem_Ioo])
  have eq5 := hpn 5 (by norm_num [Finset.mem_Ioo])
  have eq6 := hpn 6 (by norm_num [Finset.mem_Ioo])
  have eq7 := hpn 7 (by norm_num [Finset.mem_Ioo])
  have eq8 := hpn 8 (by norm_num [Finset.mem_Ioo])
  have eq9 := hpn 9 (by norm_num [Finset.mem_Ioo])
  norm_num [hp0] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 
  simp [hp1] at eq9
  linarith