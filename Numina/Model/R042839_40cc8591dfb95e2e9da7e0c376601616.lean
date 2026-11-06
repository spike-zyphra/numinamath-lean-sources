import Mathlib

theorem algebra_128598 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 2)
    (han : ∀ n ≥ 3, a n = if Even (a (n - 2) * a (n - 1)) then 5 * a (n - 1) - 3 * a (n - 2) else a (n - 1) - a (n - 2))
    (han' : ∀ n ≥ 3, a n * a (n - 1) = if Even (a (n - 2) * a (n - 1)) then 5 * a (n - 1) - 3 * a (n - 2) else a (n - 1) - a (n - 2)) :
    ∀ n, a n ≠ 0 := by
  have h3 : a 3 = if Even (a 1 * a 2) then 5 * a 2 - 3 * a 1 else a 2 - a 1 := by
    specialize han 3 (by linarith)
    simpa using han
  rw [ha1, ha2] at h3
  norm_num [Int.even_iff] at h3
  have h3' : a 3 * a 2 = if Even (a 1 * a 2) then 5 * a 2 - 3 * a 1 else a 2 - a 1 := by
    specialize han' 3 (by linarith)
    simpa using han'
  rw [ha1, ha2] at h3'
  norm_num [Int.even_iff] at h3'
  rw [show a 3 = 7 by linarith] at h3'
  all_goals omega