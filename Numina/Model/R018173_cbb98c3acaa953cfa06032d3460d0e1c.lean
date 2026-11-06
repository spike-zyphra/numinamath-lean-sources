import Mathlib

theorem number_theory_203540
    (K M N : ℤ)
    (hK : K ≠ 0)
    (hM : M ≠ 0)
    (hN : N ≠ 0)
    (hcoprime : IsCoprime K M) :
    ∃ x : ℤ, K ∣ M * x + N := by
  rcases hcoprime with ⟨s, t, h_eq⟩
  use (-N * t)
  have h_eq1 : M * t = 1 - K * s := by
    linarith
  have h_eq2 : M * (-N * t) + N = K * (N * s) := by
    calc 
      M * (-N * t) + N = -N * (M * t) + N := by ring
      _ = -N * (1 - K * s) + N := by rw [h_eq1]
      _ = -N + N * K * s + N := by ring
      _ = K * (N * s) := by ring
  rw [h_eq2]
  exact dvd_mul_right K (N * s)