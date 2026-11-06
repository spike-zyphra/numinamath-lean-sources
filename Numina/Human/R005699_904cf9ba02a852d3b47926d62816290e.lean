import Mathlib

/-
Let $\lfloor x\rfloor$ denote the largest integer less than or equal to $x$, and let $\{x\}$ denote the fractional part of $x$. For example, $\lfloor\pi\rfloor=3$, and $\{\pi\}=0.14159 \ldots$, while $\lfloor 100\rfloor=100$ and $\{100\}=0$. If $n$ is the largest solution to the equation $\frac{\lfloor n\rfloor}{n}=\frac{2015}{2016}$, compute $\{n\}$.

Answer: $2014/2015$.
-/
theorem number_theory_609479 (n : ℚ) :
  IsGreatest { a : ℚ | ⌊a⌋ / a = (2015 : ℚ) / 2016 } n → Int.fract n = ((2014 : ℚ) / 2015) := by

  simp [IsGreatest, upperBounds]

  -- Let $n$ be such that $\frac{\lfloor n\rfloor}{n}=\frac{2015}{2016}$ and
  -- is as large as possible.
  intro hn h

  -- Clearly, $n$ is not zero.
  have hnz : n ≠ 0 := by
    by_contra g
    simp [g] at hn
    revert hn
    norm_num

  -- Since $\frac{\lfloor n\rfloor}{n}=\frac{2015}{2016}$ and
  -- $n = \lfloor n\rfloor + {}n\}$,
  -- we have $\frac{\lfloor n\rfloor}{\lfloor n\rfloor + {}n\}=\frac{2015}{2016}$.
  -- Clearly fractions and simplifying gives
  -- $2016\lfloor n\rfloor = 2015\lfloor n\rfloor} + 2015\{n\}$
  have h₀ : 2016 * ⌊n⌋ = 2015 * ⌊n⌋ + 2015 * (Int.fract n) := by
    field_simp at hn
    have : n = ⌊n⌋ + Int.fract n := by exact Eq.symm (Int.floor_add_fract n)
    rw [← mul_add]
    rw [← this]
    rw [← hn]
    ring

  -- Hence, $\lfloor n\rfloor = 2015\{n\}$
  have h₁ : ⌊n⌋ = 2015 * (Int.fract n) := by
    calc
      _ = ((2016 : ℚ) - 2015) * ⌊n⌋ := by norm_num
      _ = (2016 : ℚ) * ⌊n⌋ - (2015 : ℚ) * ⌊n⌋ := by rw [sub_mul]
      _ = _ := by simp [h₀]

  -- Since $\{n\} < 1$, we have $\lfloor n\rfloor \leq 2014$.
  have h₂ : ⌊n⌋ ≤ 2014 := by
    suffices ⌊n⌋ < 2015 by exact Int.lt_add_one_iff.mp this
    qify
    rw [h₁]
    apply mul_lt_of_le_of_lt_one_of_pos
    . rfl
    . apply Int.fract_lt_one
    . norm_num

  -- Clearly, $\{n\} = 2016/2015\lfloor n\rfloor - \lfloor n\rfloor$.
  have h₃ : Int.fract n = (2016 : ℚ) / 2015 * ⌊n⌋ - ⌊n⌋ := by
    field_simp
    rw [mul_comm]
    rw [← h₁]
    ring

  -- Since $a = 2014 + 2014/2015$ satisfies
  -- $\frac{\lfloor a\rfloor}{a}=\frac{2015}{2016}$,
  -- we must have $2014 + 2014/2015 \leq n$.
  obtain hmax := @h ( (2014 : ℚ) + (2014 : ℚ) / 2015 )
  have : (2014 : ℚ) + (2014 : ℚ) / 2015 ≤ n := by
    apply hmax
    simp
    ring_nf

  -- We deduce that $2014 \leq \lfloor n \rfloor$.
  have h₄ : 2014 ≤ ⌊n⌋ := by
    apply Int.floor_le_floor at this
    ring_nf at this
    exact this

  -- Thus, $\lfloor n \rfloor = 2014$.
  have h₅ : ⌊n⌋ = 2014 := by exact Eq.symm (Int.le_antisymm h₄ h₂)

  -- It follows from $\{n\} = 2016/2015\lfloor n\rfloor - \lfloor n\rfloor$
  -- that ${}n\} = 2014/2015$.
  simp [h₅] at h₃
  rw [h₃]
  ring
