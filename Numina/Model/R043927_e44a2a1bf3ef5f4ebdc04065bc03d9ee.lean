import Mathlib

theorem number_theory_4476_1 {total removed : ℕ} (ht : total = Nat.ofDigits 12 [0, 3, 11])
    (hr : removed = Nat.ofDigits 12 [4, 7, 3]) :
    total - removed = Nat.ofDigits 12 [8, 7, 7] := by
--   So, the answer is:
-- 7 gross, 7 dozen, and 8 eggs.
  rw [ht, hr]
  native_decide

theorem number_theory_4476_2 {perLoad : ℕ} (hp : perLoad = Nat.ofDigits 12 [7, 3, 2]) :
    5 * perLoad = Nat.ofDigits 12 [11, 5, 11] := by
--   So, the answer is:
-- 11 gross, 5 dozen, and 11 eggs.
  rw [hp]
  native_decide

theorem number_theory_4476_3 {total : ℕ} (ht : total = Nat.ofDigits 12 [6, 10, 11]) :
    total = 3 * Nat.ofDigits 12 [6, 11, 3] := by
  rw [ht]
  native_decide