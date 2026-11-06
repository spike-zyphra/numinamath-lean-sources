import Mathlib

/- Let $\left(a_{n}\right)_{n \geqslant 1}$ be a sequence of positive real numbers with the property that  $$ \left(a_{n+1}\right)^{2}+a_{n} a_{n+2} \leqslant a_{n}+a_{n+2} $$  for all positive integers $n$. Show that $a_{2022} \leqslant 1$. (Nigeria) -/
theorem inequalities_24285 (a : ℕ+ → ℝ) (ha : ∀ n, 0 < a n) (h : ∀ n, (a (n + 1)) ^ 2 + a n * a (n + 2) ≤ a n + a (n + 2)) : a 2022 ≤ 1 := by
  -- We begin by observing that $\left(a_{n+1}\right)^{2}-1 \leqslant a_{n}+a_{n+2}-a_{n} a_{n+2}-1$, which is equivalent to  $$ \left(a_{n+1}\right)^{2}-1 \leqslant\left(1-a_{n}\right)\left(a_{n+2}-1\right) $$
  have h₁ (n : ℕ+) : a (n + 1) ^ 2 - 1 ≤ (1 - a n) * (a (n + 2) - 1) := by
    simp
    specialize h n
    linarith
  -- Suppose now that there exists a positive integer $n$ such that $a_{n+1}>1$ and $a_{n+2}>1$.
  by_cases h₂ : ∃n, a (n + 1) > 1 ∧ a (n + 2) > 1
  · -- Since $\left(a_{n+1}\right)^{2}-1 \leqslant\left(1-a_{n}\right)\left(a_{n+2}-1\right)$, we deduce that $0<1-a_{n}<1<1+a_{n+2}$, thus $\left(a_{n+1}\right)^{2}-1<\left(a_{n+2}+1\right)\left(a_{n+2}-1\right)=\left(a_{n+2}\right)^{2}-1$.  On the other hand, $\left(a_{n+2}\right)^{2}-1 \leqslant\left(1-a_{n+3}\right)\left(a_{n+1}-1\right) <\left(1+a_{n+1}\right)\left(a_{n+1}-1\right)=\left(a_{n+1}\right)^{2}-1$, a contradiction.
    obtain ⟨n, hn₁, hn₂⟩ := h₂
    have h₃ : 0 < 1 - a n := by
      apply pos_of_mul_pos_left
      apply lt_of_lt_of_le
      apply sub_pos_of_lt (one_lt_pow₀ hn₁ (show 2 ≠ 0 by simp))
      apply h₁
      linarith
    have h₆ : a (n + 1) ^ 2 - 1 < (a (n + 2) + 1) * (a (n + 2) - 1) := by
      apply lt_of_le_of_lt
      apply h₁
      apply mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
      have h₄ : 1 - a n < 1 := by simp [ha]
      repeat linarith
    have h₅ : (a (n + 2) + 1) * (a (n + 2) - 1) < (a (n + 1) + 1) * (a (n + 1) - 1) := by
      rw [show (a (n + 2) + 1) * (a (n + 2) - 1) = (a (n + 2)) ^ 2 - 1 by ring_nf]
      specialize h₁ (n + 1)
      rw [show (n + 1 + 1) = n + 2 by rfl] at h₁
      rw [show (1 - a (n + 1)) * (a (n + 1 + 2) - 1) = (1 - a (n + 1 + 2)) * (a (n + 1) - 1) by ring_nf] at h₁
      apply lt_of_le_of_lt
      apply h₁
      have : 1 - a (n + 1 + 2) < 1 := by simp [ha]
      apply mul_lt_mul_of_pos_right (lt_trans this (by simp [ha]))
      linarith
    linarith
  -- Finally, suppose $a_{2022}>1$. This implies that $a_{2021} \leqslant 1$ and $a_{2023} \leqslant 1$. Therefore $0<$ $\left(a_{2022}\right)^{2}-1 \leqslant\left(1-a_{2021}\right)\left(a_{2023}-1\right) \leqslant 0$, a contradiction. We conclude that $a_{2022} \leqslant 1$.
  by_contra! h₅
  have h₃ : a 2021 ≤ 1 := by
    by_contra!
    simp at h₂
    specialize h₂ 2020 this
    absurd h₂
    simp
    exact h₅
  have h₄ : a 2023 ≤ 1 := by
    simp at h₂
    exact h₂ 2021 h₅
  specialize h₁ 2021
  have h₆ : (1 - a 2021) * (a (2023) - 1) < a (2022) ^ 2 - 1 := by
    apply lt_of_le_of_lt
    apply mul_nonpos_of_nonneg_of_nonpos
    repeat linarith
    apply sub_pos_of_lt (one_lt_pow₀ h₅ (by simp))
  absurd h₁
  exact not_le_of_lt h₆
