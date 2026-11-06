import Mathlib

/- The binomial coefficients $\binom{x}{n}$, where $x$ is a variable and $n$ is a positive integer, can be defined recursively by the equations $\binom{x}{1}=x$ and
$$
\binom{x}{n+1}=\frac{x-n}{n+1}\left(\frac{x}{n}\right).
$$
a) Show that if $x$ is a positive integer, then $\binom{x}{k}=\frac{x!}{k!(x-k)!}$, where $k$ is an integer with $1 \leq k \leq x$. -/
theorem number_theory_4561_1
    (bino : ℕ → ℕ → ℕ)
    (hb_init  : ∀ x > 0, bino x 1 = x)
    (hb_other : ∀ x > 0, ∀ n > 0, bino x (n + 1) = (x - n) * (bino x n) / (n + 1))
    (hb_zero  : ∀ x > 0, bino x 0 = 1)
    (x k : ℕ) (hx : x > 0) (hk : 1 ≤ k ∧ k ≤ x) :
    bino x k = x.factorial / (k.factorial * (x - k).factorial) := by

  -- extend hb_other to n = 0
  have hb_other' : ∀ n, bino x (n + 1) = (x - n) * (bino x n) / (n + 1) := by
    intro n
    by_cases h : n = 0
    . simp [h, hb_zero x hx, hb_init x hx]
    . apply hb_other x hx n (Nat.zero_lt_of_ne_zero h)

  -- induction k
  induction k with
  | zero => linarith
  | succ k ih1 => induction k with
    -- Base Case: For k = 1,
    | zero =>
      norm_num
      rw [hb_init x hx]
      apply Nat.eq_div_of_mul_eq_right (Nat.factorial_ne_zero (x - 1))
      rw [mul_comm]
      let h := Nat.factorial_succ (x - 1)
      rw [Nat.sub_add_cancel hx] at h
      exact h.symm

    -- Inductive Step: k + 1
    | succ k ih2 =>
      set kk := k + 1
      have : (x - kk).factorial = (x - kk) * (x - (kk + 1)).factorial := by
        rw [show x - (kk + 1) = x - kk - 1 by rfl]
        let h := Nat.factorial_succ (x - kk - 1)
        rw [Nat.sub_add_cancel (Nat.zero_lt_sub_of_lt hk.right)] at h
        exact h
      rw [hb_other', ih1 ⟨Nat.le_add_left 1 k, Nat.le_of_succ_le hk.right⟩]
      rw [Nat.factorial_succ kk]
      rw [this]
      have : (x - kk) * (x.factorial / (kk.factorial * ((x - kk) * (x - (kk + 1)).factorial))) / (kk + 1) = x.factorial / ((kk + 1) * kk.factorial * (x - (kk + 1)).factorial) := sorry
      exact this

/- b) Show that $\binom{x}{n}+\binom{x}{n+1}=\binom{x+1}{n+1}$, whenever $n$ is a positive integer. -/
theorem number_theory_4561_2
    (x n : ℕ) :
    x.choose n + x.choose (n + 1) = (x + 1).choose (n + 1) := by
  exact rfl
