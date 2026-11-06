import Mathlib

theorem number_theory_45493 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hinc : ∀ n, a n ≤ a (n + 1)) (hbound : ∀ n, a (n + 1) ≤ a n + 5)
    (hdiv : ∀ n, n ≤ a n → n ∣ a n) :
    a 1 = 26 := by
  -- For n = 0, apply the divisibility condition
  have h1 := hdiv 0
  -- Show that $0 \le a_0$ is automatically true
  have h2 : (0 : ℕ) ≤ a 0 := by
    omega
  -- Let's derive $0 \mid a_0$ from h1 and h2
  have h3 := h1 h2
  -- $0 \mid a 0$ contradicts because it would imply $a 0 = 0$ while $a 0 \ge 1$
  have h4 : a 0 = 0 := by
    rcases h3 with ⟨k, hk⟩
    omega
  have h8 : a 0 > 0 := ha 0
  omega