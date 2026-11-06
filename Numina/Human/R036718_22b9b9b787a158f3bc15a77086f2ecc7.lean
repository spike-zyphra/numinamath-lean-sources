import Mathlib

/- [ [ Properties of the module. Triangle inequality ]

Given a sequence of positive numbers $q_{1}, \ldots, q_{n}, \ldots$, a sequence of polynomials is constructed as follows:

$$

\begin{aligned}
& f_{0}(x)=1 \\
& f_{1}(x)=x \\
& \ldots \\
& f_{n+1}(x)=\left(1+q_{n}\right) x f_{n}(x)-q_{n} f_{n-1}(x)
\end{aligned}

$$

Prove that all real roots of the $n$-th polynomial are contained between -1 and 1.

# -/
theorem algebra_190911 (q : ℕ → ℝ) (hq : ∀ i > 0, q i > 0)
    (f : ℕ → ℝ → ℝ) (hf0 : ∀ x, f 0 x = 1) (hf1 : ∀ x, f 1 x = x)
    (hfn : ∀ n > 0, ∀ x, f (n + 1) x = (1 + q n) * x * f n x - q n * f (n - 1) x) :
    ∀ n x, f n x = 0 → x ∈ Set.Icc (-1) 1 := by
  -- Prove by induction that |f n x| < |f (n + 1) x| for all 1 < |x|
  have h {x} (hx : 1 < |x|): ∀ n, |f n x| < |f (n + 1) x| := by
    intro n
    induction n with
    -- |f 0 x| = 1 and |f 1 x| = |x| so the result follows from the assumption 1 < |x|.
    | zero => rw [hf0, hf1, abs_one]; linarith
    | succ n ih =>
      replace hq : 0 < q (n + 1) := hq (n + 1) (by omega)
      -- We have
      -- |f (n + 2) x| = |(1 + q (n + 1)) * x * f (n + 1) x - q (n + 1) * f n x|
      --               ≥ |(1 + q (n + 1)) * x * f (n + 1) x| - |q (n + 1) * f n x| (because |a - b| ≥ |a| - |b| for any a and b)
      --               = |x| * |f (n + 1) x| + q (n + 1) * (|x| * |f (n + 1) x| - |f n x|) (because q (n + 1) > 0)
      --               > 1 * |f (n + 1) x| + 0 (because |x| > 1 and |f (n + 1) x| > |f n x| by the induction hypothesis)
      calc
        |f (n + 2) x| = |(1 + q (n + 1)) * x * f (n + 1) x - q (n + 1) * f n x| := by rw [hfn _ (by omega)]; rfl
        _ ≥ |(1 + q (n + 1)) * x * f (n + 1) x| - |q (n + 1) * f n x| := abs_sub_abs_le_abs_sub _ _
        _ = |x| * |f (n + 1) x| + q (n + 1) * (|x| * |f (n + 1) x| - |f n x|) := by
            simp_rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + q (n + 1) by positivity), abs_of_nonneg (le_of_lt hq)]
            ring
        _  > 1 * |f (n + 1) x| + 0 := by
            gcongr
            · linarith [abs_nonneg (f n x)]
            · apply mul_pos hq
              suffices 1 * |f n x| < |x| * |f (n + 1) x| by linarith
              gcongr
        _ = |f (n + 1) x| := by simp only [one_mul, add_zero]
  -- Now it is easy to show that 1 ≤ |f n x| for all 1 < |x|.
  have h1 {x} (hx : 1 < |x|) : ∀ n, 1 ≤ |f n x| := by
    intro n
    induction n with
    | zero => rw [hf0, abs_one]
    | succ n ih => linarith [h hx n]
  intro n x hfx0
  -- Assume that f n x = 0 and show that x ∈ [-1, 1].
  by_cases hx : 1 < |x|
  -- Suppose that 1 < |x|.
  -- Then we have 1 ≤ |f n x| = |0| = 0, a contradiction.
  · have := h1 hx n
    rw [hfx0, abs_zero] at this
    norm_num at this
  -- If |x| ≤ 1 then x ∈ [-1, 1].
  · simp only [lt_abs, not_or, not_lt, Set.mem_Icc] at hx ⊢
    constructor <;> linarith