import Mathlib

theorem number_theory_283308 (V M S : ℕ) (hV : V = 35) (hM : M < V) (hS : S = V + M)
    (hEven : Even S) :
    V + M + S ≤ 136 := by
  rw [hV] at hM
  rw [hS, hV] at hEven
  rw [hV, hS]
  have h1 : M < 35 := by linarith
  have h2 : (35 + M) % 2 = 0 := by
    rcases hEven with ⟨k, hk⟩
    omega
  have h3 : M % 2 = 1 := by
    omega
  omega