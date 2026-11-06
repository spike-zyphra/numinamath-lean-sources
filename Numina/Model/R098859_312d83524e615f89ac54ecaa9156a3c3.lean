import Mathlib

theorem algebra_269470 (P : ℕ → ℕ) (hP : ∀ n, P n = P (n - 4) * 2) (hP0 : P 0 = 3456) :
    P 10 = 108 := by 
  have h0 := hP 0
  simp at h0 hP0
  all_goals omega