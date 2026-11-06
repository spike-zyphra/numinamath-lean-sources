import Mathlib

/- a) If 3 gross, 7 dozen, and 4 eggs are removed from a total of 11 gross and 3 dozen eggs, how many eggs are left? -/
theorem number_theory_4476_1 {total removed : ℕ} (ht : total = Nat.ofDigits 12 [0, 3, 11])
    (hr : removed = Nat.ofDigits 12 [4, 7, 3]) :
    total - removed = Nat.ofDigits 12 [8, 7, 7] := by
--   So, the answer is:
-- 7 gross, 7 dozen, and 8 eggs.
  rw [ht, hr]
  native_decide

/- b) If 5 truckloads of 2 gross, 3 dozen, and 7 eggs each are delivered to the supermarket, how many eggs were delivered? -/
theorem number_theory_4476_2 {perLoad : ℕ} (hp : perLoad = Nat.ofDigits 12 [7, 3, 2]) :
    5 * perLoad = Nat.ofDigits 12 [11, 5, 11] := by
--   So, the answer is:
-- 11 gross, 5 dozen, and 11 eggs.
  rw [hp]
  native_decide

/- c) If 11 gross, 10 dozen, and 6 eggs are divided into 3 groups of equal size, how many eggs are in each group? -/
theorem number_theory_4476_3 {total : ℕ} (ht : total = Nat.ofDigits 12 [6, 10, 11]) :
    total = 3 * Nat.ofDigits 12 [6, 11, 3] := by
--   So, the answer is:
-- 3 gross, 11 dozen, and 6 eggs.
  rw [ht]
  native_decide
