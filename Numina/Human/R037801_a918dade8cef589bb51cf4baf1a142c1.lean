import Mathlib

open Real

/- Determine whether there exists an infinite sequence $a_{1}, a_{2}, a_{3}, \ldots$ of positive integers which satisfies the equality

$$
a_{n+2}=a_{n+1}+\sqrt{a_{n+1}+a_{n}}
$$

for every positive integer n.
(Japan) -/
theorem number_theory_604649 : false =
    ∃ a : ℕ → ℕ, (∀ n > 0, 0 < a n) ∧ (∀ n > 0, a (n + 2) = a (n + 1) + √(a (n + 1) + a n))  := by
    -- Suppose that there exists a sequence $\left(a_{n}\right)$ of positive integers satisfying the given condition.
    by_contra h
    simp at h
    obtain ⟨a, ha, h⟩ := h
    -- For each $n \geq 2$ define $b_{n}=a_{n+1}-a_{n}$.
    let b := fun n => a (n + 1) - a n
    -- the sequence $\left(a_{n}\right)$ is strictly increasing for $n \geq 2$.
    have h0 : ∀ n ≥ 2, a n < a (n + 1) := by
      intro n hn
      specialize h (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] at h
      suffices √(↑(a n) + ↑(a (n - 1))) > 0 by
        suffices (a n : ℝ) < a (n + 1) by rwa [Nat.cast_lt] at this
        linarith
      apply sqrt_pos.mpr
      apply add_pos
      simp [ha n (by linarith)]
      simp [ha (n - 1) (by omega)]
    -- Then, by assumption, for $n \geq 2$ we get $b_{n}=\sqrt{a_{n}+a_{n-1}}$
    have h1 : ∀ n ≥ 2, b n = √(a n + a (n - 1)) := by
      intro n hn
      simp [b]
      rw [Nat.cast_sub (by linarith [h0 n hn]), sub_eq_iff_eq_add]
      specialize h (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] at h
      simp [h, add_comm]
    -- Since each $a_{n}$ is a positive integer we see that $b_{n}$ is a positive integer for $n \geq 2$
    have h2 : ∀ n ≥ 2, b n > 0 := by
      intro n hn
      suffices (b n : ℝ) > 0 by rwa [gt_iff_lt, Nat.cast_pos] at this
      rw [h1 n hn]
      apply sqrt_pos.mpr
      apply add_pos
      simp [ha n (by linarith)]
      simp [ha (n - 1) (by omega)]
    -- and the sequence $\left(b_{n}\right)$ is strictly increasing for $n \geq 3$.
    have h3 : ∀ n ≥ 3, b n < b (n + 1) := by
      intro n hn
      suffices (b n : ℝ) < b (n + 1) by rwa [Nat.cast_lt] at this
      rw [h1 n (by linarith), h1 (n + 1) (by linarith)]
      apply sqrt_lt_sqrt (by linarith)
      norm_cast
      simp
      apply add_lt_add
      · exact h0 n (by linarith)
      · specialize h0 (n - 1) (by omega)
        rw [show n - 1 + 1 = n by omega] at h0
        linarith
    -- $$ b_{n+1}^{2}-b_{n}^{2}=\left(a_{n+1}+a_{n}\right)-\left(a_{n}+a_{n-1}\right)=\left(a_{n+1}-a_{n}\right)+\left(a_{n}-a_{n-1}\right)=b_{n}+b_{n-1} . $$
    have h4 : ∀ n ≥ 3, b (n + 1) ^ 2 - b n ^ 2 = b n + b (n - 1) := by
      intro n hn
      suffices (b (n + 1) : ℝ) ^ 2 - b n ^ 2 = b n + b (n - 1) by
        rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub, ← Nat.cast_add] at this
        norm_cast at this
        apply pow_le_pow (by linarith [h3 n hn]) _ (by norm_num)
        specialize h2 (n + 1) (by linarith)
        omega
      nth_rw 1 [h1 n (by linarith), h1 (n + 1) (by linarith), sq_sqrt (by linarith), sq_sqrt (by linarith)]
      simp [b]
      rw [show n - 1 + 1 = n by omega, Nat.cast_sub (by linarith [h0 n (by linarith)]),
        Nat.cast_sub]
      · ring_nf
      · specialize h0 (n - 1) (by omega)
        rw [show n - 1 + 1 = n by omega] at h0
        linarith
    -- Thus $b_{n}+b_{n-1}=\left(b_{n+1}-b_{n}\right)\left(b_{n+1}+b_{n}\right) \geq b_{n+1}+b_{n}$, whence $b_{n-1} \geq b_{n+1}$
    have h5 : ∀ n ≥ 3, b (n - 1) ≥ b (n + 1) := by
      intro n hn
      suffices b n + b (n - 1) ≥ b n + b (n + 1) by linarith
      rw [← h4 n (by linarith), Nat.sq_sub_sq, add_comm]
      suffices (b (n + 1) - b n) ≥ 1 by
        simp
        apply Nat.le_mul_of_pos_right
        specialize h3 n (by linarith)
        omega
      specialize h3 n (by linarith)
      omega
    -- a contradiction to the increasing nature of the sequence $\left(b_{i}\right)$.
    linarith [h3 3 (by norm_num), h5 4 (by norm_num), h3 4 (by norm_num)]