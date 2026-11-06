import Mathlib

theorem algebra_10569 {x : ℤ} (hx : x > 0) (n d : ℤ)
    (hn : n = x ^ 2 + 2 * x + 17) (hd : d = 2 * x + 5)
    (hdiv : n / d = x ∧ n % d = 7) : x = 2 := by
  rcases hdiv with ⟨h1, h2⟩
  have h_eq1 : n = x * d + 7 := by
    rw [←Int.ediv_add_emod n d, h1, h2]
    all_goals ring
  rw [hn, hd] at h_eq1
  have h_eq2 : x ^ 2 + 3 * x - 10 = 0 := by
    nlinarith [h_eq1]
  have h_eq3 : x ^ 2 + 3 * x - 10 = (x - 2) * (x + 5) := by
    ring
  rw [h_eq3] at h_eq2
  cases' (mul_eq_zero.1 h_eq2) with h_eq4 h_eq5
  · -- Case $x - 2 = 0$, so $x = 2$
    linarith
  · -- Case $x + 5 = 0$, so $x = -5$, which contradicts with $x > 0$
    linarith