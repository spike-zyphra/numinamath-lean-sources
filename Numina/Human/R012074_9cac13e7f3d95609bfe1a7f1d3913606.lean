import Mathlib

open Polynomial Nat Int

theorem algebra_172807 (P : ℤ[X]) {k : ℤ} (hP : P.eval 1 = 2013) (hP' : P.eval 2013 = 1) (hk : P.eval k = k) : k = 1007 := by 
  have dvd1 : k - 1 ∣ P.eval k - P.eval 1 := by 
    exact sub_dvd_eval_sub k 1 P
  rw [hk, hP] at dvd1
  have dvd2 : k - 2013 ∣ P.eval k - P.eval 2013 := by
    exact sub_dvd_eval_sub k 2013 P
  rw [hk, hP'] at dvd2
  obtain h2 := Int.natAbs_eq_of_dvd_dvd dvd1 dvd2
  obtain h3 := Int.natAbs_eq_natAbs_iff.mp h2
  obtain heq | heq := h3
  linarith
  linarith