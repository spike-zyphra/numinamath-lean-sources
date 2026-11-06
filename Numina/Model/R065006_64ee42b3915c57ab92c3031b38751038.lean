import Mathlib

theorem number_theory_232428 {N : ℕ} (hN : N < 100 ∧ N > 9)
    (h1 : 5655 % N = 11) (h2 : 5879 % N = 14) :
    (Nat.digits 10 N).sum = 8 := by
  rcases hN with ⟨hN1, hN2⟩
  interval_cases N <;> norm_num at h1 h2 ⊢ <;> all_goals
    native_decide