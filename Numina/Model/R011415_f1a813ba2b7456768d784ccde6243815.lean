import Mathlib

theorem number_theory_243206 {n: ℕ} (a b c d: ℕ)
(hn: n = 1000 * a + 100 * b + 10 * c + d) (h: a + b + c + d = 27):
  27 ∣ (n + (1000 * d + 100 * c + 10 * b + a)) := by
  rw [hn]
  have h1 : (1000 * a + 100 * b + 10 * c + d) + (1000 * d + 100 * c + 10 * b + a) = 1001 * a + 110 * b + 110 * c + 1001 * d := by 
    omega 
  rw [h1] 
  have h2 : 1001 * a + 110 * b + 110 * c + 1001 * d = 1001 * (a + d) + 110 * (b + c) := by 
    ring 
  rw [h2] 
  have h3 : a + d = 27 - (b + c) := by 
    omega 
  rw [h3] 
  -- Now the goal is to show 27 divides `1001 * (27 - (b + c)) + 110 * (b + c)`.
  ring_nf 
  all_goals omega