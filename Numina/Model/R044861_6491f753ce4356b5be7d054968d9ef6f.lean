import Mathlib

theorem number_theory_237959 (x : ℕ → ℕ)
    (hx : ∀ n, x n = if (9 ∣ n ∧ 32 ∣ n) then 7 else (if (7 ∣ n ∧ 32 ∣ n) then 9 else (if (7 ∣ n ∧ 9 ∣ n) then 32 else 0))) :
    ∑ i in Finset.range 2015, x (i + 1) = 1106 := by
  rw [Finset.sum_congr rfl (fun i _ => hx (i + 1))]
  native_decide