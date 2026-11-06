import Mathlib

/- The function $f(n)$ is defined on the positive integers such that $f(f(n)) = 2n$ and $f(4n + 1) = 4n + 3$ for all positive integers $n.$  Find $f(1000).$ -/
theorem algebra_12668 {f : ℕ → ℕ} (hf : ∀ n, 0 < n → f (f n) = 2 * n ∧ f (4 * n + 1) = 4 * n + 3) :
    f 1000 = 1016 := by
  -- since f(f(n)) = 2n, suppose a = f(n), then f(a) = 2n and f(f(a)) = 2a, f (2a) = f( f(f(a)) ) = f(f(  f(a)  )) = 2f(a).
  have h1: ∀a:ℕ, 0 < a → 0 < f a → f (2*a) = 2 * f a := by
    intro a ha hfa
    -- f(f(a)) = 2a
    have ht1 := (hf a ha).left
    rw [← ht1]
    apply (hf (f a) hfa).left
  -- notice that 125 = 4x31 + 1, fo f(4x31+1)=4x31+3=127
  have h2: f 125 = 127 := by
    have ht1: 125 = 4 * 31 + 1 := by ring
    have ht2: 0 < 31 := by norm_num
    rw [ht1, (hf 31 ht2).right]
  -- repeatedly using h1, f(1000)=2f(500)=4f(250)=8f(125)
  have h3: 2*(2*(2*f 125)) = f 1000 := by
    have ht1: 0 < 125 := by norm_num
    have ht2: 0 < f 125 := by
      rw [h2]; norm_num
    rw [← h1 125 ht1 ht2]; simp
    have ht3: 0 < 250 := by norm_num
    have ht4: 0 < f 250 := by
      have: 250 = 2*125 := by norm_num
      rw [this, h1 125 ht1 ht2]; linarith [ht2]
    rw [← h1 250 ht3 ht4]; simp
    have ht5: 0 < 500 := by norm_num
    have ht6: 0 < f 500 := by
      have: 500 = 2*250 := by norm_num
      rw [this, h1 250 ht3 ht4]; linarith [ht4]
    rw [← h1 500 ht5 ht6]
  -- therefore f(1000)=8f(125)=8x127=1016
  rw [← h3, h2]