import Mathlib

/-7. A7 (ARM) Let $f$ be a function from the set of real numbers $\mathbb{R}$ into itself such that for all $x \in \mathbb{R}$, we
 have $|f(x)| \leq 1$ and  $$ f\left(x+\frac{13}{42}\right)+f(x)=f\left(x+\frac{1}{6}\right)+f\left(x+\frac{1}{7}\right) . $$
  Prove that $f$ is a periodic function (that is, there exists a nonzero real number $c$ such that $f(x+c)=f(x)$ for all $x \in \mathbb{R})$. -/
theorem algebra_24773 (f : ℝ → ℝ) (h : ∀ x : ℝ, |f x| ≤ 1) (h1 : ∀ x : ℝ, f (x + 13 / 42) + f x = f (x + 1/6) + f (x + 1/7)) : ∃ c : ℝ, c ≠ 0 ∧ ∀ x : ℝ, f (x + c) = f x := by
  -- we introduce a = 1 / 6, b = 1 / 7 and rewrite the equation as f (x + a + b) + f x = f (x + a) + f (x + b)
  let a:= (1 : ℝ) / 6
  let b:= (1 : ℝ) / 7
  have ha : a = 1 / 6:= by rfl
  have hb : b = 1 / 7:= by rfl
  clear_value a b
  have h2 : a + b = 13 / 42:= by linarith
  rw [←ha, ←hb, ←h2] at h1
  -- we show that f (x + a + 1) - f (x + a) = f (x + 1) - f x for all x
  replace h1 : ∀ x, f (x + a + 1) - f (x + a) = f (x + 1) - f x:= by
    intro x
    -- just substitute x, x + b, x + 2 * b, x + 3 * b, x + 4 * b, x + 5 * b, x + 6 * b into the equation h1
    have g1:= h1 x
    have g2:= h1 (x + b)
    have g3:= h1 (x + 2 * b)
    have g4:= h1 (x + 3 * b)
    have g5:= h1 (x + 4 * b)
    have g6:= h1 (x + 5 * b)
    have g7:= h1 (x + 6 * b)
    -- use b * 7 = 1 and linarith
    ring_nf at g1 g2 g3 g4 g5 g6 g7
    rw [show b * 7 = 1 by linarith] at g7
    linarith
  -- we show that f (x + 2) - f (x + 1) = f (x + 1) - f x for all x
  replace h1 : ∀ x, f (x + 2) - f (x + 1) = f (x + 1) - f x:= by
    intro x
    -- just substitute x, x + a, x + 2 * a, x + 3 * a, x + 4 * a, x + 5 * a, x + 6 * a into the equation h1
    have g1:= h1 x
    have g2:= h1 (x + a)
    have g3:= h1 (x + 2 * a)
    have g4:= h1 (x + 3 * a)
    have g5:= h1 (x + 4 * a)
    have g6:= h1 (x + 5 * a)
    -- use a * 6 = 1 and linarith
    ring_nf at g1 g2 g3 g4 g5 g6
    rw [show a * 6 = 1 by linarith] at g6
    ring_nf at g6
    ring_nf
    linarith
  -- we prove by induction that f (x + n) - f x = n * (f (x + 1) - f x) for all x real and n integer
  have h3 : ∀ x, (∀ n : ℕ, f (x + n) - f x = n * (f (x + 1) - f x)):= by
    intro x n
    induction n with
    -- base case n = 0 is by simp
    | zero =>
      simp
    | succ n ih =>
      -- to prove the inductive step, we show that f (x + m + 1) - f (x + m) = f (x + 1) - f x by induction on m
      have h4 : ∀ n : ℕ, f (x + n + 1) - f (x + n) = f (x + 1) - f x:= by
        intro m
        induction m with
        -- base case m = 0 is by simp
        | zero =>
          simp
        -- inductive step is inductive hypothesis and h1 (x + m)
        | succ m ih1 =>
          simp
          ring_nf
          specialize h1 (x + m)
          ring_nf at ih1 h1
          linarith
      -- specialize h4 with n
      specialize h4 n
      simp
      ring_nf at ih h4
      ring_nf
      linarith
  -- now we show that c = 1 actually works by contradiction
  use 1
  simp
  intro x
  by_contra H
  specialize h3 x
  -- by assumption, we have e ≠ 0
  let e:= f (x + 1) - f x
  have he : e = f (x + 1) - f x:= by rfl
  clear_value e
  rw [←he] at h3
  replace H : e ≠ 0:= by
    rw [he]
    by_contra!
    replace this : f (x + 1) = f x:= by linarith
    trivial
  -- thus |e| > 0
  replace H : |e| > 0:= by exact abs_pos.mpr H
  -- we show that ∀ n : ℕ, ↑n ≤ (|f x| + 1) / |e|
  replace h3 : ∀ n : ℕ, n ≤ (|f x| + 1) / |e|:= by
    intro n
    specialize h3 n
    -- apply the abs_sub theorem
    have h4 : |f (x + n)| + |f x| ≥ |f (x + n) - f x|:= by exact abs_sub (f (x + n)) (f x)
    rw [h3] at h4
    -- we have n ≥ 0
    have h5 : n ≥ 0:= by omega
    rify at h5
    -- apply the abs_mul theorem
    have h6 : |n * e| = |(n : ℝ)| * |e|:= by exact abs_mul (n : ℝ) e
    rw [show |(n : ℝ)| = n by exact Nat.abs_cast n] at h6
    rw [h6] at h4
    specialize h (x + n)
    have h7 : n * |e| ≤ |f x| + 1:= by linarith
    exact (le_div_iff₀ H).mpr h7
  -- we get that ∀ n : ℕ, ↑n ≤ t, which is a contradiction by setting n = ⌊t⌋ + 1
  let t:= (|f x| + 1) / |e|
  have ht : t = (|f x| + 1) / |e|:= by rfl
  clear_value t
  rw [←ht] at h3
  specialize h3 (⌊t⌋.natAbs + 1)
  simp at h3
  -- use ⌊t⌋ + 1 > t
  have h4 : ⌊t⌋ + 1 > t:= by exact Int.lt_floor_add_one t
  have h5 : ⌊t⌋ ≤ ⌊t⌋.natAbs:= by exact Int.le_natAbs
  have h6 : (⌊t⌋.natAbs : ℝ) = (⌊t⌋.natAbs : ℤ):= by exact rfl
  rify at h5 h6
  linarith
