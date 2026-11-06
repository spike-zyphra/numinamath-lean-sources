import Mathlib

/-
Problem

The function $f(x)$ satisfies $f(x+5)=f(x)$ for all real numbers $x$, and when $x ∈ []0,5)$, $f(x)=x^2-x$. Find the value of $f(2008)$.
-/

/-
Solution

Since $f(x)$ satisfies $f(x+5)=f(x)$ for all real numbers $x$, we have:
$$f(2008)=f(5×401+3)$$
$$=f(3),$$
because when $x \in [0,5)$, $f(x)=x^2-x$. Therefore,
$$f(2008)=f(3)=9-3=6.$$
Hence, the answer is $\boxed{6}$.
-/


theorem algebra_8986 {f : ℝ → ℝ} (h : ∀ x, f (x + 5) = f x)
    (hf : ∀ x ∈ Set.Ico 0 5, f x = x ^ 2 - x) :
    f 2008 = 6 := by
      -- prove that $f (x + 5n) = f (x)$.
      have np : ∀ n : ℕ, ∀ x : ℝ, f (x + n * 5) = f x := by
        intro n x
        -- indcution on $n$
        induction' n with d hd
        -- the equation is obivious when $n = 0$
        · simp only [CharP.cast_eq_zero, zero_mul, add_zero]
        · have : (x + (d + 1) * 5) = ((x + d * 5) + 5) := by
            rw [add_assoc]
            have : (d * 5) + 5 = (d + 1) * 5 := by ring
            ring
          -- type coersion
          push_cast
          rw [this]
          obtain foo := h (x + d * 5)
          rw [foo]
          exact hd
      -- decompose $2008$
      have : (2008 : ℝ) = 3 + 5 * 401 := by
        norm_num
      rw [this]
      obtain bar := np 401 3
      rw [mul_comm]
      -- type coersion
      norm_cast; norm_cast at bar
      rw [bar]
      -- $3 \in [0, 5)$
      have in0to5 : (3 : ℝ) ∈ Set.Ico 0 5 := by
        simp only [Set.mem_Ico, Nat.ofNat_nonneg, true_and]
        linarith
      obtain baz := hf 3 (in0to5)
      rw [baz]
      -- simply calculate it
      norm_num