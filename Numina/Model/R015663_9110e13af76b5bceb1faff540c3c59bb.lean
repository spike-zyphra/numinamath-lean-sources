import Mathlib

theorem algebra_102586 {p : Polynomial ℤ} (hp : ∀ m n, (p.eval m - p.eval n) ∣ (m^2 - n^2))
    (hp0 : p.eval 0 = 1) (hp1 : p.eval 1 = 2) :
    p.eval 100 ≤ 10001 := by
  have h1 : (p.eval 100 - p.eval 0) ∣ (100 ^ 2 - 0 ^ 2) := hp 100 0
  rw [hp0] at h1
  have h2 : (p.eval 100 - 1) ∣ (100 ^ 2) := by
    simpa using h1
  have h3 : (p.eval 100 - p.eval 1) ∣ (100 ^ 2 - 1 ^ 2) := hp 100 1
  rw [hp1] at h3
  have h4 : (p.eval 100 - 2) ∣ (100 ^ 2 - 1) := by
    simpa using h3
  have h7 : p.eval 100 - 1 ∣ 10000 := by
    norm_num at h2 ⊢
    exact h2
  -- From divisibility, we have $p(100) - 1$ divides $10000$.
  have h10 : p.eval 100 - 1 ≤ 10000 := by
    apply Int.le_of_dvd (by norm_num) h7
  have h11 : p.eval 100 ≤ 10001 := by 
    omega
  linarith