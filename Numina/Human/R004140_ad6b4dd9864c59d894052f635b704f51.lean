import Mathlib

open Finset

/-
Consider the sequence $a_{k}$ defined by $a_{1}=1, a_{2}=\frac{1}{2}$,

$$
a_{k+2}=a_{k}+\frac{1}{2} a_{k+1}+\frac{1}{4 a_{k} a_{k+1}} \quad \text { for } k \geq 1
$$

Prove that

$$
\frac{1}{a_{1} a_{3}}+\frac{1}{a_{2} a_{4}}+\frac{1}{a_{3} a_{5}}+\cdots+\frac{1}{a_{98} a_{100}}<4
$$
 -/
theorem algebra_239170
    (a : ℕ → ℝ)
    (ha1 : a 1 = 1)
    (ha2 : a 2 = 1 / 2)
    (hak : ∀ k ≥ 1, a (k + 2) = a k + (1 / 2) * a (k + 1) + (1 / (4 * a k * a (k + 1)))) :
    ∑ i ∈ range 98, 1 / (a (i + 1) * a (i + 3)) < 4 := by
  /-
  Note that

  $$ \frac{1}{a_{k} a_{k+2}}a_{k}+\frac{1}{2} a_{k+1} $$

  which is evident for the given sequence.
   -/
  -- This proposition from the reference solution seems incomplete.
  /-
  Now we have

  $$ \begin{aligned} \frac{1}{a_{1} a_{3}}+\frac{1}{a_{2} a_{4}} & +\frac{1}{a_{3} a_{5}}+\cdots+\frac{1}{a_{98} a_{100}} \\ & < \frac{2}{a_{1} a_{2}}-\frac{2}{a_{2} a_{3}}+\frac{2}{a_{2} a_{3}}-\frac{2}{a_{3} a_{4}}+\cdots \\ & < \frac{2}{a_{1} a_{2}}=4 \end{aligned} $$
  -/
  let rec a_pos : ∀ k > 0, a k > 0
    --| 0, nomatch => by nomatch gt
    | 1, _ => by simp [ha1]
    | 2, _ => by simp [ha2]
    | k' + 3, _ => by
      specialize hak (k' + 1) (by linarith)
      rw [show k' + 1 + 1 = k' + 2 from rfl] at hak
      rw [hak]
      have := a_pos (k' + 1) (by linarith)
      have := a_pos (k' + 2) (by linarith)
      --norm_num
      --nlinarith
      positivity
  have lt_1 : ∑ i ∈ range 98, 1 / (a (i + 1) * a (i + 3)) < ∑ i ∈ range 98, (2 / (a (i + 1) * a (i + 2)) - 2 / (a (i + 2) * a (i + 3))) := by
    apply sum_lt_sum_of_nonempty
    . simp
    . intro i _
      have := a_pos (i + 1) (by simp)
      have := a_pos (i + 2) (by simp)
      have := a_pos (i + 3) (by simp)
      suffices a (i + 2) / (a (i + 1) * a (i + 2) * a (i + 3)) <
          2 * a (i + 3) / (a (i + 1) * a (i + 2) * a (i + 3)) -
          2 * a (i + 1) / (a (i + 1) * a (i + 2) * a (i + 3)) by
        convert this using 1
        . field_simp
          ring
        . congr 1 <;>
          . field_simp
            ring
      suffices a (i + 2) < 2 * a (i + 3) - 2 * a (i + 1) by
        --nlinarith
        field_simp
        set a_prod := a (i + 1) * a (i + 2) * a (i + 3)
        /-
        have : a_prod > 0 := by
          --nlinarith
          positivity
        field_simp [this]
         -/
        gcongr
      have := hak (i + 1) (by simp)
      have : 1 / (4 * a (i + 1) * a (i + 1 + 1)) > 0 := by
        positivity
      linarith
  have : ∑ i ∈ range 98, (2 / (a (i + 1) * a (i + 2)) - 2 / (a (i + 2) * a (i + 3))) =
      2 / (a 1 * a 2) - 2 / (a 99 * a 100) := by
    rw [Finset.sum_sub_distrib]
    have : ∑ x ∈ range 98, 2 / (a (x + 2) * a (x + 3)) =
        ∑ x ∈ Ico 1 99, 2 / (a (x + 1) * a (x + 2)) := by
      rfl
    rw [this]
    rw [←Finset.sum_sdiff_sub_sum_sdiff]
    have : range 98 \ Ico 1 99 = {0} := by
      ext
      simp
      omega
    rw [this]
    have : Ico 1 99 \ range 98 = {98} := by
      ext
      simp
      omega
    rw [this]
    simp
  rw [this] at lt_1
  have : 2 / (a 1 * a 2) - 2 / (a 99 * a 100) < 2 / (a 1 * a 2) := by
    suffices 2 / (a 99 * a 100) > 0 by
      linarith
    have a_99_pos := a_pos 99 (by simp)
    have a_100_pos := a_pos 100 (by simp)
    positivity --field_simp [/- a_99_pos, -/ a_100_pos]
  conv_rhs at this => norm_num [ha1, ha2]
  linarith
