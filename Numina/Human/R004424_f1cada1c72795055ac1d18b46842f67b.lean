import Mathlib

open Real Set

-- we write a lemma to simplify the problem using |x|
lemma lemma_1 (x: ℝ): x ∈ Iio (-8) ∪ Ioo (-7) 0 ∪ Ioo 0 7 ∪ Ioi 8 ↔
  |x| ∈ Ioo 0 7 ∪ Ioi 8 := by

  simp
  constructor

  -- the forward direction
  .
    intro h
    rcases h with h | h
    .
      rcases h with h | h
      .
        rcases h with h | h
        .
          right
          rw [lt_abs]
          right
          linarith
        .
          left
          constructor
          .
            by_contra! o
            simp [o] at h
          .
            rw [abs_lt]
            constructor
            .
              linarith
            .
              linarith
      .
        left
        constructor
        .
          by_contra! o
          simp [o] at h
        .
          rw [abs_lt]
          constructor
          .
            linarith
          .
            linarith
    .
      right
      rw [lt_abs]
      left
      tauto

  -- the backward direction
  .
    intro h
    rcases h with h | h
    .
      rcases h with ⟨ne, h⟩
      rw [abs_lt] at h
      by_cases s: 0 < x
      .
        left
        right
        simp [s]
        linarith
      .
        left
        left
        right
        simp at s
        constructor
        linarith
        by_contra! o
        replace o: x = 0 := by linarith
        tauto
    .
      rw [lt_abs] at h
      rcases h with h | h
      .
        right
        tauto
      .
        left
        left
        left
        linarith


/-
 Solve the inequality $\quad \frac{|x|+21-7 \sqrt{|x|+9}}{x^{2}-8|x|}>0$

ОДЗ: $x \neq 0, \quad x \neq \pm 8$.

Разложим числитель на множители:

$$ |x|+21-7 \sqrt{|x|+9}=|x|+9-7 \sqrt{|x|+9}+12=(\sqrt{|x|+9})^{2}-7 \sqrt{|x|+9}+12=(\sqrt{|x|+9}-3)(\sqrt{|x|+9}-4) $$

Имеем:

$$ \frac{(\sqrt{|x|+9}-3)(\sqrt{|x|+9}-4)}{|x|(|x|-8)} > 0 \Leftrightarrow \frac{(|x|+9-9)(|x|+9-16)}{|x|(|x|-8)} > 0 \Leftrightarrow \frac{|x|(|x|-7)}{|x|(|x|-8)} > 0 $$

Решая методом интервалов, получаем $\quad|x| \in(0 ; 7) \cup(8 ;+\infty)$.

Имеем $x \in(-\infty ;-8) \cup(-7 ; 0) \cup(0 ; 7) \cup(8 ;+\infty)$

Ответ: $x \in(-\infty ;-8) \cup(-7 ; 0) \cup(0 ; 7) \cup(8 ;+\infty)$ -/

theorem inequalities_264692 (x : ℝ) (n1: x ≠ 0) (n2: x ≠ 8) (n3: x ≠ -8):
  (|x| + 21 - 7 * sqrt (abs x + 9)) / (x^2 - 8 * abs x) > 0 ↔
  x ∈ Iio (-8) ∪ Ioo (-7) 0 ∪ Ioo 0 7 ∪ Ioi 8 := by

  -- we use the symmetry to simplify using y = |x|
  rw [lemma_1]
  rw [show x ^ 2 = |x| ^ 2 by simp]
  set y:= |x|
  replace n1: y ≠ 0 := by
    simp [y]
    tauto
  replace n2: y ≠ 8 := by
    simp [y]
    rw [show (8: ℝ) = |8| by norm_num]
    rw [abs_eq_iff_mul_self_eq]
    by_contra! o
    replace o: (x - 8) * (x + 8) = 0 := by
      nlinarith
    simp at o
    rcases o with o | o
    .
      absurd n2
      linarith
    .
      absurd n3
      linarith
  clear n3
  have ly: 0 < y := by
    suffices 0 ≤ y by
      positivity
    simp [y]
  clear_value y

  simp [ly]
  rw [div_pos_iff]
  constructor

  -- the forward direction
  .
    intro h
    by_contra! l
    rcases l with ⟨l, r⟩
    set p:= y + 21 - 7 * √(y + 9)
    set q:= y ^ 2 - 8 * y
    absurd h
    suffices 0 ≤ p ∧ q ≤ 0 by
      clear_value p q
      clear *- this
      by_contra! g
      rcases this with ⟨u, v⟩
      rcases g with g | g
      .
        absurd v
        simp
        linarith
      .
        absurd u
        simp
        linarith
    constructor
    .
      simp [p]
      suffices √(y + 9) ≤ (y + 21) / 7 by nlinarith
      rw [Real.sqrt_le_iff]
      constructor
      .
        linarith
      .
        nlinarith
    .
      simp [q]
      nlinarith

  -- the backward direction
  .
    intro h
    rcases h with h | h
    .
      right
      constructor
      .
        suffices (y + 21) / 7 < √(y + 9) by linarith
        apply Real.lt_sqrt_of_sq_lt
        nlinarith
      .
        nlinarith

    .
      left
      constructor
      .
        suffices √(y + 9) < (y + 21) / 7 by linarith
        rw [Real.sqrt_lt']
        .
          nlinarith
        .
          linarith
      .
        nlinarith
