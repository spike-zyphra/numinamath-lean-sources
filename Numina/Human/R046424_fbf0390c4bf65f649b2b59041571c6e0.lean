import Mathlib

/- ## Task 1.
Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function with the following properties:
(a) There exists a real number $M$ such that $|f(x)| \leqslant M$ for all $x \in \mathbb{R}$.
(b) For every real number $x$,
$$
f\left(x+\frac{1}{2}\right)+f\left(x+\frac{1}{3}\right)=f(x)+f\left(x+\frac{5}{6}\right)
$$
Show that the function $f$ is periodic, that is, there exists a positive real number $T$ such that $f(x+T)=f(x)$ for all $x \in \mathbb{R}$. -/
theorem algebra_250413 (f : ℝ → ℝ) (hM : ∃ M, ∀ x, |f x| ≤ M)
    (hf : ∀ x, f (x + 1 / 2) + f (x + 1 / 3) = f x + f (x + 5 / 6)) :
    ∃ T, 0 < T ∧ Function.Periodic f T := by
  -- Define g(x) = f(x) - f(x + 1/2).
  set g : ℝ → ℝ := fun x => f x - f (x + 1 / 2)
  -- Define h(x) = f(x) - f(x + 1).
  set h : ℝ → ℝ := fun x => f x - f (x + 1)
  -- Show that g is periodic with period 1 / 3.
  have hg : g.Periodic (1 / 3) := by
    intro x
    calc
      -- We have g(x + 1/3) = f(x + 1/3) - f(x + 5/6)
      --                    = f(x) - f(x + 1/2) (this result follows from hf)
      --                    = g(x).
      g (x + 1 / 3) = f (x + 1 / 3) - f (x + 5 / 6) := by
          dsimp [g]
          norm_num [add_assoc]
      _ = f x - f (x + 1 / 2) := by linarith [hf x]
      _ = g x := rfl
  -- Show that h is periodic with period 1.
  have hh : h.Periodic 1 := by
    intro x
    calc
      -- We have
      -- h(x + 1) = g(x - (-3) * 1/3) + g(x + 1/2 - (-3) * (1/3))
      --          = g(x) + g(x + 1/2) (because g is periodic with period 1/3)
      --          = h(x).
      h (x + 1) = g (x - (-3 : ℤ) * (1 / 3)) + g (x + 1 / 2 - (-3 : ℤ) * (1 / 3)) := by
          simp [h, g, add_assoc]
          norm_num
      _ = g x + g (x + 1 / 2) := by simp_rw [hg.sub_int_mul_eq]
      _ = h x := by
          simp [g, h, add_assoc]
          norm_num
  -- Prove that f(x) - f(x + n) = n * h(x) for all x and for all natural n.
  have hfn x (n : ℕ) : f x - f (x + n) = n * h x := by
    -- Proof by induction.
    induction n with
    -- If n = 0 then f(x) - f(x) = 0 = 0 * h(x).
    | zero => simp
    | succ n ih => calc
      -- Consider n + 1:
      -- f(x) - f(x + (n + 1)) = f(x) - f(x + n) + h(x - (-n) * 1)
      --                       = n * h(x) + h(x)
      -- (f(x) - f(x + n) = n * h(x) from the induction hypothesis
      --  and h(x - (-n) * 1) = h(x) because h is periodic with period 1).
      f x - f (x + (n + 1 : ℕ)) = f x - f (x + n) +  h (x - (-n : ℤ) * 1) := by
          simp [h, add_assoc]
      _ = n * h x + h x := by rw [ih, hh.sub_int_mul_eq]
      _ = (n + 1 : ℕ) * h x := by push_cast; ring
  -- Show that f is periodic with period 1.
  use 1, zero_lt_one
  intro x
  -- We have |f(x)| ≤ M for all x for some constant M.
  replace ⟨M, hM⟩ := hM
  -- Assume that f(x + 1) ≠ f(x) and derive a contradiction.
  by_contra hf1
  -- Find a natural number n such that 2 * M / |h(x)| < n (note that h(x) = f(x) - f(x + 1) ≠ 0).
  have ⟨n, hn⟩ := exists_nat_gt (2 * M / |h x|)
  -- Show that f(x + 1) ≠ f(x) implies that 2 * M < M + M.
  suffices 2 * M < M + M by linarith
  calc
    -- We have 2 * M < n * |h(x)| (because n > 2 * M / |h(x)| and h(x) ≠ 0).
    2 * M < n * |h x| := by
        apply (div_lt_iff₀ _).mp hn
        simp_rw [abs_pos, h, sub_ne_zero]
        exact Ne.symm hf1
    -- n * |h(x)| = |f(x) - f(x + n)|
    --            ≤ |f(x)| + |f(x + n)|
    --            ≤ M + M.
    _ = |f x - f (x + n)| := by simp [hfn, abs_mul]
    _ ≤ |f x| + |f (x + n)| := abs_sub (f x) (f (x + ↑n))
    _ ≤ M + M := by gcongr <;> apply hM