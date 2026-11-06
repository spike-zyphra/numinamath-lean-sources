import Mathlib

/- 18. Let the function $f(x)$ defined on the set of rational numbers satisfy: for any $a, b \in \mathbf{Q}_{+}$, we have

$$

f(a b)=f(a)+f(b),

$$


and for each prime number $p$, we have $f(p)=p$. Then when the value of $x$ is $(\quad)$, we have $f(x)<0$.
(A) $\frac{17}{32}$
(B) $\frac{11}{16}$
(C) $\frac{7}{9}$
(D) $\frac{7}{6}$
(E) $\frac{25}{11}$ -/
theorem number_theory_202097 (f : ℚ → ℝ) (h : ∀ a b, 0 < a → 0 < b → f (a * b) = f a + f b)
    (hp : ∀ p, Nat.Prime p → f p = p) :
    f (25 / 11) < 0 := by
  -- first prove f (1) = 0 as f(2*1) = f(2) + f(1)
  have h1 : f 1 = 0 := by
    have h2 := hp 2 (by norm_num)
    have h2' := h2
    nth_rw 1 [show ↑(2 : ℕ) = (2 * 1 : ℚ) by norm_cast] at h2
    rw [h _ _ (by norm_num) (by norm_num)] at h2
    rw [show ↑(2 : ℕ) = (2 : ℚ) by norm_cast] at h2'
    linarith
  -- next prove that 0 = f(1) = f(p * (1/p)) = f(p) + f(1/p) = p + f(1/p), so f(1/p) = -p for primes
  have hp' (p : ℕ) (hp' : Nat.Prime p) : f (1 / p) = -p := by
    have : 0 < (p : ℚ) := by norm_num; exact Nat.Prime.pos hp'
    have : f (p * (1 / p)) = 0 := by
      field_simp
      assumption
    rw [h _ _ (by assumption) (by positivity), hp _ hp'] at this
    linarith
  -- now write 25/11 as (5 * 5) * (1/11) then the result is f(5) + f(5) + f(1/11) = 5 + 5 - 11  = -1
  have hv : f (25 / 11) = -1 := by calc
    f (25 / 11) = f (25 * (1 / 11)) := by ring_nf
    _ = f 25 + f (1 / 11) := by apply h <;> norm_num
    _ = f (5 * 5) + f (1 / ↑(11 : ℕ)) := by
      norm_num
    _ = f 5 + f 5 + (- 11) := by
      congr
      . apply h <;> norm_num
      . apply hp'
        norm_num
    _ = -1 := by
      rw [show (5 : ℚ) = ↑(5 : ℕ) by norm_cast, hp _ (by norm_num)]
      norm_num
  rw [hv]
  norm_num