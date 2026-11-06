import Mathlib

theorem number_theory_134564 (m n : ℤ) (h : Odd m) (h' : Odd n)
    (h'' : m = n + 2) :
    8 ∣ 7 * m^2 - 5 * n^2 - 2 := by 
  rw [h'']
  rcases h with ⟨k, hk⟩
  rcases h' with ⟨l, hl⟩
  have h_eq : k = l + 1 := by
    have eq : 2 * k + 1 = 2 * l + 3 := by linarith [hk, hl]
    linarith
  have eq1 : (n + 2) = 2 * l + 3 := by 
    rw [show n = 2 * l + 1 by linarith [hl]]
    linarith
  rw [eq1, show n = 2 * l + 1 by linarith [hl]]
  ring_nf
  <;> use l^2 + 8 * l + 7
  <;> ring