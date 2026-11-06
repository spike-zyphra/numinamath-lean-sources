import Mathlib

open Classical

/- 6 Given a function $y=f(x)$ defined on the set of all real numbers that satisfies $f(x+2 \pi)=f(x)$, and the functions

$$

\begin{array}{l}
g(x)=\frac{f(x)+f(-x)}{2}, \\
h(x)=\frac{f(x)-f(-x)}{2} .
\end{array}

$$


If the functions $p(x)$ and $q(x)$ are defined as

$$

\begin{array}{c}
p(x)=\left\{\begin{array}{cc}
\frac{g(x)-g(x+\pi)}{2 \cos x} & \left(x \neq k \pi+\frac{\pi}{2}\right), \\
0 & \left(x=k \pi+\frac{\pi}{2}\right),
\end{array}\right. \\
q(x)=\left\{\begin{array}{cc}
\frac{h(x)+h(x+\pi)}{2 \sin 2 x} & \left(x \neq \frac{k \pi}{2}\right), \\
0 & \left(x=\frac{k \pi}{2}\right),
\end{array}\right.
\end{array}

$$


where $k \in \mathbf{Z}$, then which of the following statements about $p(x)$ and $q(x)$ is correct? ( ).
(A) Both are odd functions with a period of $\pi$
(B) Both are even functions with a period of $\pi$
(C) Neither has odd or even properties but both have periodicity
(D) Neither has periodicity but both have odd or even properties -/
theorem algebra_249853 (f g h p q: ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
  (hg : g = fun x => (f x + f (-x)) / 2)
  (hh : h = fun x => (f x - f (-x)) / 2)
  (hp : p = fun x : ℝ => if (∀ k: ℤ, x ≠ k * Real.pi + Real.pi / 2) then (g x - g (x + Real.pi)) / (2 * Real.cos x) else 0)
  (hq : q = fun x => if (∀ k: ℤ, x ≠ k * Real.pi / 2) then (h x + h (x + Real.pi)) / (2 * Real.sin (2 * x)) else 0)
  : Function.Even p ∧ Function.Even q ∧ Function.Periodic p Real.pi ∧ Function.Periodic q Real.pi := by
    -- g is even
    have g_even : Function.Even g := by
      intro x
      simp only [hg, neg_neg, add_comm]

    -- h is odd
    have h_odd : Function.Odd h := by
      intro x
      rw [hh]
      ring_nf

    -- g is periodic
    have g_periodic : Function.Periodic g (2 * Real.pi) := by
      intro x
      rw [hg]
      simp only []
      rw [hf]
      congr 2
      convert_to f ((-x) + (-1 : ℤ) * (2 * Real.pi)) = f (-x)
      · ring_nf
      exact Function.Periodic.int_mul hf (-1) (-x)

    -- h is periodic
    have h_periodic : Function.Periodic h (2 * Real.pi) := by
      intro x
      rw [hh]
      simp only []
      congr 2
      exact hf x
      convert_to f ((-x) + (-1 : ℤ) * (2 * Real.pi)) = f (-x)
      · ring_nf
      exact Function.Periodic.int_mul hf (-1) (-x)

    -- We note elementary relations between x = k * π + π / 2 (resp. x = k * π / 2), implying representations of and -x and x + π
    have neg_pi : ∀ x, (∀ k : ℤ, x ≠ k * Real.pi + Real.pi / 2) → (∀ k : ℤ, -x ≠ k * Real.pi + Real.pi / 2)
      := by
      intro x xh k'
      have xhh := xh (-k' - 1)
      push_cast at xhh
      by_contra hh
      have hy : x = -(k' : ℝ) * Real.pi - Real.pi / 2 := by linarith
      ring_nf at hy xhh
      exact False.elim (xhh hy)

    have neg_pi' : ∀ x, (∀ k: ℤ, x ≠ k * Real.pi / 2) → (∀ k: ℤ, -x ≠ k * Real.pi / 2) := by
      intro x xh k'
      have xhh := xh (-k')
      push_cast at xhh
      by_contra hh
      refine absurd ?_ xhh
      linarith

    have neg_pi_not' : ∀ x, ¬(∀ k: ℤ, x ≠ k * Real.pi / 2) → ¬(∀ k: ℤ, -x ≠ k * Real.pi / 2) := by
      intro x xh con
      have goo := neg_pi' (-x) con
      simp only [neg_neg, ne_eq] at goo
      exact absurd goo xh

    have neg_pi_not : ∀ x, ¬(∀ k : ℤ, x ≠ k * Real.pi + Real.pi / 2) → ¬(∀ k : ℤ, -x ≠ k * Real.pi + Real.pi / 2)
      := by
      intro x xh con
      have goo := neg_pi (-x) con
      simp only [neg_neg, ne_eq] at goo
      exact absurd goo xh

    have pi_add : ∀ x, (∀ k : ℤ, x ≠ k * Real.pi + Real.pi / 2) → (∀ k : ℤ, x + Real.pi ≠ k * Real.pi + Real.pi / 2) := by
      intro x xh k'
      by_contra hh
      have yeah := xh (k' - 1)
      push_cast at yeah
      have gg : x = ↑k' * Real.pi + Real.pi / 2 - Real.pi := by linarith
      rw [gg] at yeah
      ring_nf at yeah
      exact absurd rfl yeah

    have pi_add_not : ∀ x, ¬(∀ k : ℤ, x ≠ k * Real.pi + Real.pi / 2) → ¬(∀ k : ℤ, x + Real.pi ≠ k * Real.pi + Real.pi / 2) := by
      intro x xh con
      simp only [ne_eq, not_forall, Decidable.not_not] at xh
      obtain ⟨k'', kh''⟩ := xh
      have ne := pi_add (x + Real.pi) con (k'' + 2)
      rw [kh''] at ne
      push_cast at ne
      ring_nf at ne
      exact absurd rfl ne

    have pi_add' : ∀ x, (∀ k : ℤ, x ≠ k * Real.pi / 2) → (∀ k : ℤ, x + Real.pi ≠ k * Real.pi / 2) := by
      intro x xh k'
      by_contra hh
      have yeah := xh (k' - 2)
      push_cast at yeah
      have gg : x = ↑k' * Real.pi / 2 - Real.pi := by linarith
      rw [gg] at yeah
      ring_nf at yeah
      exact absurd rfl yeah

    have pi_add_not' : ∀ x, ¬(∀ k : ℤ, x ≠ k * Real.pi / 2) → ¬(∀ k : ℤ, x + Real.pi ≠ k * Real.pi / 2) := by
      intro x xh con
      simp only [ne_eq, not_forall, Decidable.not_not] at xh
      obtain ⟨k'', kh''⟩ := xh
      have ne := pi_add' (x + Real.pi) con (k'' + 4)
      rw [kh''] at ne
      push_cast at ne
      ring_nf at ne
      exact absurd rfl ne

    -- Now we prove properties of p and q
    refine ⟨?_, ?_, ?_, ?_⟩
    -- p is even
    · intro x
      rw [hp]
      -- Is x = k * Real.pi + Real.pi / 2 for some k ∈ Z?
      by_cases xh : (∀ k : ℤ, x ≠ k * Real.pi + Real.pi / 2)
      -- if x isn't, then -x isn't
      · have neg_xh := neg_pi x xh
        simp only [ne_eq, neg_xh, not_false_eq_true, implies_true, ↓reduceIte, Real.cos_neg, xh]
        congr 2
        · exact g_even x
        · convert_to g ((-x - Real.pi) + 2 * Real.pi) = g (x + Real.pi)
          · ring_nf
          rw [g_periodic (-x - Real.pi), ←g_even]
          ring_nf
      · have neg_xh_not := neg_pi_not x xh
        simp only [ne_eq, neg_xh_not, ↓reduceIte, xh]
    -- q is even
    · intro x
      rw [hq]
      -- Is x = k * Real.pi / 2 for some k ∈ Z?
      by_cases xh : (∀ k: ℤ, x ≠ k * Real.pi / 2)
      -- if x isn't, then -x isn't
      · have neg_xh' := neg_pi' x xh
        simp only [ne_eq, neg_xh', not_false_eq_true, implies_true, ↓reduceIte, mul_neg,
          Real.sin_neg, xh]
        rw [←neg_div_neg_eq]
        simp only [neg_add_rev, neg_neg]
        congr 1
        rw [←h_odd (-x + Real.pi)]
        simp only [neg_add_rev, neg_neg]
        rw [add_comm]
        rw [h_odd x]
        simp only [neg_neg, add_right_inj]
        convert_to h ((-Real.pi + x) + 2 * Real.pi) = h (x + Real.pi)
        · exact (h_periodic (-Real.pi + x)).symm
        ring_nf
      · have neg_xh_not' := neg_pi_not' x xh
        simp only [ne_eq, neg_xh_not', ↓reduceIte, xh]
    -- p has period π
    · intro x
      rw [hp]
      -- Is x = k * Real.pi + Real.pi / 2 for some k ∈ Z?
      by_cases xh : (∀ k : ℤ, x ≠ k * Real.pi + Real.pi / 2)
      -- if x isn't, then x + π isn't
      · have xh_add := pi_add x xh
        simp only [ne_eq, xh_add, not_false_eq_true, implies_true, ↓reduceIte, Real.cos_add_pi,
          mul_neg, xh]
        rw [←neg_div_neg_eq]
        simp only [neg_sub, neg_neg]
        congr 2
        ring_nf
        rw [mul_comm]
        exact g_periodic x
      · have xh_add_not := pi_add_not x xh
        simp only [ne_eq, xh_add_not, ↓reduceIte, xh]

    -- q has period π
    · intro x
      rw [hq]
      -- Is x = k * Real.pi / 2 for some k ∈ Z?
      by_cases xh : (∀ k: ℤ, x ≠ k * Real.pi / 2)
      -- if x isn't, then x + π isn't
      · have xh_add' := pi_add' x xh
        simp only [ne_eq, xh_add', not_false_eq_true, implies_true, ↓reduceIte, xh]
        congr 1
        · rw [add_comm]
          congr 1
          ring_nf
          rw [mul_comm]
          exact h_periodic x
        · congr 1
          convert_to Real.sin (2 * x + ((2 : ℤ) : ℝ) * Real.pi) = Real.sin (2 * x)
          · ring_nf
          simp only [Int.cast_ofNat, Real.sin_add_two_pi]
      · have xh_add_not := pi_add_not' x xh
        simp only [ne_eq, xh_add_not, ↓reduceIte, xh]