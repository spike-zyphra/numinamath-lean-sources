import Mathlib

theorem number_theory_95741 {n : ℕ} (hn : n = 33) :
    ¬(6 ∣ (Nat.digits 10 n).sum → 6 ∣ n) := by
  rw [hn]
  intro h
  have h1 : 6 ∣ (Nat.digits 10 (33 : ℕ)).sum := by
    native_decide
  have h2 : ¬ (6 ∣ (33 : ℕ)) := by
    norm_num
  have h3 : 6 ∣ (33 : ℕ) := by
    apply h
    exact h1
  contradiction