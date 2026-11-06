import Mathlib

theorem number_theory_159870 (T : ℕ → ℤ) (hT : ∀ n, T n = 11^(n + 2) + 12^(2 * n + 1)) :
    ∀ n, 133 ∣ T n := by 
  intro n 
  induction n with 
  | zero =>
    have h1 : T 0 = 133 := by 
      rw [hT 0]
      norm_num 
    rw [h1]
    all_goals norm_num 
  | succ n ih =>
    -- Induction hypothesis: 133 divides T n
    have eq1 : T (n + 1) = 11 * (T n) + 133 * (12 : ℤ) ^ (2 * n + 1) := by 
      rw [hT (n + 1), hT n]
      ring_nf 
      <;> omega
    rw [eq1]
    omega