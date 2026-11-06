import Mathlib

theorem number_theory_169875 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Nat.lcm x y = 51975 ∧ Nat.gcd x y = 45 ∧ x = 4725) :
    y = 495 := by
  rcases hxy with ⟨hl, hg, hx_eq⟩
  rw [hx_eq] at hl hg
  have key := Nat.gcd_mul_lcm 4725 y
  rw [hg, hl] at key
  have h1 : 4725 * y = 2338875 := by
    linarith
  have h2 : y = 495 := by
    omega
  exact h2