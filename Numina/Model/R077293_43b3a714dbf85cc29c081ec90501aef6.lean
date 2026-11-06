import Mathlib

theorem algebra_286875 {l p : ℕ} (hl : l > 0) (hp : p > 0)
    (hperim : 2 * (l + p) = 63) (hlength : p = 2 * (l + 2)) :
    l * p = 17 := by 
  omega