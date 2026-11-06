import Mathlib

/- 5. The function $f(x)$ defined on $\mathbf{R}$, for any real number $x$, satisfies

$$

\begin{array}{l}
f(x+3) \leqslant f(x)+3, \\
f(x+2) \geqslant f(x)+2,
\end{array}

$$


and $f(1)=2$. Let $a_{n}=f(n)\left(n \in \mathbf{Z}_{+}\right)$, then

$$

f(2015)=

$$
 -/
theorem algebra_228718 (f : ℝ → ℝ) (h₁ : ∀ x, f (x + 3) ≤ f x + 3) (h₂ : ∀ x, f (x + 2) ≥ f x + 2)
    (h₃ : f 1 = 2) : f 2015 = 2016 := by
  -- Show that f(x) + 3 ≥ f(x + 1) + 2 for all x.
  have h1 x : f x + 3 ≥ f (x + 1) + 2 := calc
    f x + 3 ≥ f (x + 3) := h₁ x
    _ = f (x + 1 + 2) := by ring_nf
    _ ≥ f (x + 1) + 2 := h₂ (x + 1)
  -- Show that f(x) + 4 ≤ f(x + 1) + 3 for all x.
  have h2 x : f x + 4 ≤ f (x + 1) + 3 := calc
    f x + 4 = (f x + 2) + 2 := by ring
    _ ≤ f (x + 2) + 2 := by gcongr; exact h₂ _
    _ ≤ f (x + 2 + 2) := h₂ (x + 2)
    _ = f (x + 1 + 3) := by ring_nf
    _ ≤ f (x + 1) + 3 := h₁ (x + 1)
  -- From h1 and h2 we derive that f(x + 1) = f(x) + 1 for all x.
  have h_eq x : f (x + 1) = f x + 1 := by linarith [h1 x, h2 x]
  -- Prove by induction that f(n) = n + 1 for all natural n.
  have h (n : ℕ) : f n = n + 1 := by
    induction n with
    -- If n = 0 then 2 = f(1) = f(0) + 1, so f(0) = 1 = 0 + 1.
    | zero =>
      specialize h_eq 0
      simp at h_eq ⊢
      linarith
    -- For n + 1 we have:
    -- f(n + 1) = f(n) + 1 = (n + 1) + 1.
    | succ n ih =>
      simp [h_eq, ih]
  -- We compute f(2015) = 2015 + 1 = 2016.
  rw [show (2015 : ℝ) = (2015 : ℕ) by simp, h]
  norm_num