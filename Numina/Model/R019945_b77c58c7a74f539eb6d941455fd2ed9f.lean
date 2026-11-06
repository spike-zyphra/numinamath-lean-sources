import Mathlib

open Real

theorem algebra_313823 {a b : ℕ → ℝ}
    (ha : ∀ n, a n = (2 + sqrt 7)^(2 * n + 1))
    (hb : ∀ n, b n = a n - ⌊a n⌋) :
    ∀ n > 0, Odd (a n * b n) := by
  intro n hn
  rw [hb n, ha n]
  use ( ( (2 + sqrt 7) ^ (2 * n + 1) * ( (2 + sqrt 7) ^ (2 * n + 1) - ⌊ (2 + sqrt 7) ^ (2 * n + 1) ⌋ ) - 1 ) / 2 )
  ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num