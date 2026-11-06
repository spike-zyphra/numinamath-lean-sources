import Mathlib

theorem number_theory_106592 {n k : ℕ} (hn : n > 20) (hk : k > 1)
    (hdiv : k^2 ∣ n) : ∃ a b c, n = a * b + b * c + c * a := by
  rcases hdiv with ⟨m, hm⟩
  use (k * m)
  use 0
  use k
  all_goals nlinarith [hm]