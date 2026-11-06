import Mathlib

open Nat

theorem number_theory_7720 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
  (h : ∃ n, n^2 = a * b + 1) :
  ∃ c : ℕ, 0 < c ∧ ∃ m, m^2 = a * c + 1 ∧ ∃ p, p^2 = b * c + 1 := by
    rcases h with ⟨n, hn⟩
    use a + b + 2 * n
    constructor
    · -- $c > 0$ because $a > 0$, $b > 0$, and $n \geq 1$ (since $n^2 = ab + 1 \geq 1$)
      nlinarith [ha, hb, hn]
    · refine ⟨a + n, by 
        nlinarith [hn], ⟨b + n, by nlinarith [hn]⟩⟩