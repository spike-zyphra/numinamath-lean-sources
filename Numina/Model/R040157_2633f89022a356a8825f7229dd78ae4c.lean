import Mathlib

theorem algebra_308887 {a b : ℕ → ℤ} (ha : ∀ n, a n = 4 * n - 1)
    (hb : ∀ n, b n = a n ∧ ¬(3 ∣ a n) ∧ ¬(5 ∣ a n)) :
    b 2006 = 15043 := by
  have h1 := hb 1
  have ha1 : a 1 = 4 * 1 - 1 := ha 1
  rw [ha1] at h1
  norm_num at h1
  all_goals omega