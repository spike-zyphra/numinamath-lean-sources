import Mathlib.Tactic

theorem number_theory_141542 (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ)
    (ha : ∀ i, 0 < a i) :
    1 / 4 ≤ {x : Fin 3 → Fin n | 3 ∣ a (x 0) + a (x 1) + a (x 2)}.ncard / n ^ 3 := by
  have h1 : 1 / 4 = 0 := by norm_num
  have h2 : {x : Fin 3 → Fin n | 3 ∣ a (x 0) + a (x 1) + a (x 2)}.ncard / n ^ 3 ≥ 0 := by
    apply Nat.zero_le
  simp [h1, h2]
  all_goals omega