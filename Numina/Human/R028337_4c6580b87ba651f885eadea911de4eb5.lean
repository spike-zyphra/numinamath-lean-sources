import Mathlib

/- 19. （MEX 1)Let $f ( n )$ be a function defined on the set of all positive integers and having its values in the same set. Suppose that $f ( f ( m )+f ( n ) )=m+n$ for all positive integers $n, m$ . Find all possible values for $f ( 1 9 8 8 )$ . -/
theorem algebra_24132 (f : ℤ → ℤ) (h1 : ∀ x > 0, f x > 0) (h2 : ∀ m > 0, ∀ n > 0, f (f m + f n) = m + n) : f 1988 = 1988 := by
  -- first we show that f n + f m is a function of (n + m) by showing that f (f 1 + n + m) = 1 + f n + f m
  have g1 : ∀ m > 0, ∀ n > 0, f (f 1 + n + m) = 1 + f n + f m := by
    -- rewrite n + m as f (f n + f m)
    intro m hm n hn
    have g2:= h2 n hn m hm
    rw [(show f 1 + n + m = f 1 + (n + m) by ring_nf), ←g2]
    have g3 := h1 n hn
    have g4 := h1 m hm
    -- then apply h2 for 1 and f n + f m
    specialize h2 1 (by omega) (f n + f m) (by omega)
    simp [h2]
    linarith
  -- then we show that f (n + 1) + f 1 = f n + f 2 because (n + 1) + 1 = n + 2, which is induced by g1
  have g2 : ∀ n > 0, f (n + 1) + f 1 = f n + f 2 := by
    intro n hn
    have g3 := g1 (n + 1) (by omega) 1 (by omega)
    have g4 := g1 n hn 2 (by omega)
    rw [show f 1 + 1 + (n + 1) = f 1 + 2 + n by ring_nf] at g3
    omega
  clear g1
  -- next, we show that f n is an arithmetic sequence with difference f 2 - f 1 by induction
  have g1 : ∀ (n : ℕ), n ≥ 1 → f ↑n = ↑n * (f 2 - f 1) + 2 * f 1 - f 2:= by
    intro n hn
    induction n, hn using Nat.le_induction with
    -- prove the base case by direct calculation
    | base =>
      simp
      ring_nf
    | succ m hm ih =>
      -- prove the inductive step by induction hypothesis and g2 (m + 1)
      specialize g2 m (by omega)
      rw [show (↑(m + 1) : ℤ) = ↑m + 1 by norm_num]
      replace g2 : f (↑m + 1) = f ↑m + f 2 - f 1:= by linarith
      rw [g2, ih]
      linarith
  -- reform g1 as a lemma of integer n
  replace g1 : ∀ n ≥ 1, f n = n * (f 2 - f 1) + 2 * f 1 - f 2:= by
    intro n hn
    specialize g1 (n.natAbs) (by omega)
    simp at g1
    rw [show |n| = n by exact abs_of_pos hn] at g1
    exact g1
  -- the key equation, which is to substitute f n and f m into h2 and get a explicit equation
  replace h2 : ∀ m > 0, ∀ n > 0, (m + n) * ((f 2 - f 1) ^ 2 - 1) + (4 * f 1 - 2 * f 2) * (f 2 - f 1) + 2 * f 1 - f 2 = 0:= by
    intro m hm n hn
    specialize h2 m hm n hn
    -- get the explicit expression of f n and f m
    have g3 := g1 m (by omega)
    have g4 := g1 n (by omega)
    rw [g3, g4] at h2
    -- the positivity of f n and f m
    have g5 := h1 n (by omega)
    have g6 := h1 m (by omega)
    rw [g3] at g6
    rw [g4] at g5
    -- refine the expressions
    rw [show m * (f 2 - f 1) + 2 * f 1 - f 2 + (n * (f 2 - f 1) + 2 * f 1 - f 2) = (m + n) * (f 2 - f 1) + 4 * f 1 - 2 * f 2 by ring_nf] at h2
    have g7 := g1 ((m + n) * (f 2 - f 1) + 4 * f 1 - 2 * f 2) (by linarith)
    rw [g7] at h2
    linarith
  -- the const term is zero
  have h3 : (4 * f 1 - 2 * f 2) * (f 2 - f 1) + 2 * f 1 - f 2 = 0:= by
    have g3 := h2 1 (by omega) 1 (by omega)
    have g4 := h2 1 (by omega) 2 (by omega)
    linarith
  -- the arithmetic sequence difference is 1
  have h4 : (f 2 - f 1) ^ 2 - 1 = 0:= by
    have g5 := h2 1 (by omega) 2 (by omega)
    linarith
  have h5 : f 2 - f 1 = 1:= by
    -- prove that f 2 ≥ f 1 by positivity assumption
    have g3 : f 2 - f 1 ≥ 0:= by
      by_contra H
      simp at H
      -- f 1 > 0
      have g4 := h1 1 (by omega)
      specialize g1 (f 1 + 1) (by omega)
      specialize h1 (f 1 + 1) (by omega)
      -- f 2 - f 1 + 1 ≤ 0
      replace H : f 2 - f 1 + 1 ≤ 0:= by omega
      rw [show (f 1 + 1) * (f 2 - f 1) + 2 * f 1 - f 2 = f 1 * (f 2 - f 1 + 1) by linarith] at g1
      rw [g1] at h1
      -- get the contradiction
      nlinarith only [g4, H, h1]
    replace h4 : (f 2 - f 1 - 1) * (f 2 - f 1 + 1) = 0:= by linarith
    have g4 : f 2 - f 1 + 1 ≠ 0:= by omega
    suffices f 2 - f 1 - 1 = 0 by linarith
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero g4 h4
  replace h5 : f 2 = f 1 + 1:= by linarith
  rw [h5] at h3
  ring_nf at h3
  -- so f 1 = 1 and f 2 = 2
  replace h3 : f 1 = 1:= by linarith
  replace h5 : f 2 = 2:= by linarith
  simp [h3, h5] at g1
  -- use g1 to finish the proof
  specialize g1 1988 (by omega)
  exact g1
