import Mathlib

theorem number_theory_151138 {x : ℕ} (hx : x ≥ 1000) (hxp : x < 10000)
    (hxp1 : (x / 100) + 1 = 100 * (x % 100) + 10 * ((x / 100) % 100) + 1)
    (hxp2 : 11 * (100 * (x / 100) + 10 * ((x / 100) % 100) + 1) ∣ x) :
    x = 1960 := by
  have h1 : x < 10000 := hxp
  have h2 : x ≥ 1000 := hx
  have h3 : x / 100 < 100 := by
    omega
  have h4 : (x / 100) % 100 = x / 100 := by
    omega
  simp [h4] at hxp1
  omega