import Mathlib

open Real Set
open scoped BigOperators

/- 9. (2000 Beijing Competition Problem Adapted) Let the function $f(x), x \in \mathbf{N}^{+}$, satisfy $f(x+1)=\sin \left[\frac{\pi}{2} \cdot f(x)\right]$, $f(1)=\frac{1}{2}$. Prove: $1-f(x)<\frac{\pi}{4}[1-f(x-1)](x \geqslant 2)$. -/
theorem algebra_148847 {f : ℕ → ℝ} (h₁ : ∀ x, f (x + 1) = sin (π / 2 * f x)) (h₂ : f 0 = 1 / 2) :
    ∀ x, 1 - f (x + 1) < (π / 4) * (1 - f x) := by
  -- statement is shifted by 1 down for ease of work
  -- first we write 1 - f(x+1) in terms of cos and sin
  have h₃ (x : ℕ) : 1 - f (x + 1) = 2 * cos (π / 4 * (1 + f x)) * sin (π / 4 * (1 - f x)) := by
    rw [h₁]
    nth_rw 1 [← sin_pi_div_two]
    rw [sin_sub_sin, mul_assoc, mul_comm (sin _), ← mul_assoc]
    ring_nf
  -- determine value of f(1) using sin
  have h₄ : f 1 = √2 / 2 := by
    rw [h₁, h₂]
    convert_to sin (π/4) = _
    . ring_nf
    rw [sin_pi_div_four]
  -- now we'll prove using induction that 1/2 ≤ f (x) < f(x + 1) < 1
  have h₅ (x : ℕ) : 1 / 2 ≤ f x ∧ f x < f (x + 1) ∧ f (x + 1) < 1 := by
    induction' x with m hm
    -- using f(0), f(1) for base case
    . rw [h₂, h₄]
      norm_num
      and_intros
      . rw [show (1 : ℝ) = √1 by simp]
        gcongr; norm_num
      . rw [show (1 : ℝ) = √(2^2) / 2 by simp]
        gcongr; norm_num
    -- for inductive case, multiply inequalities by π / 2
    . have h1 : π / 2 * (1 / 2) ≤ π / 2 * f m := by gcongr; exact hm.left
      have h2 : π / 2 * f m  < π / 2 * f (m + 1) := by gcongr; exact hm.right.left
      have h3 : π / 2 * f (m + 1) < π / 2 * 1 := by gcongr; exact hm.right.right
      and_intros
      -- then prove goals by using sin's monotoneness
      . rw [h₁]
        suffices √2 / 2 ≤ sin (π / 2 * f m) by
          refine le_trans ?_ this
          gcongr; simp
        rw [← sin_pi_div_four]
        apply Real.strictMonoOn_sin.monotoneOn
        . and_intros <;> linarith
        . and_intros <;> linarith
        . linarith
      . rw [h₁, h₁]
        apply Real.strictMonoOn_sin
        . and_intros <;> linarith
        . and_intros <;> linarith
        . linarith
      . rw [h₁, ← sin_pi_div_two]
        apply Real.strictMonoOn_sin
        . and_intros <;> linarith
        . and_intros <;> linarith
        . linarith
  -- now prove 0 < 2 * cos (π / 4 * (1 + f x)) < 1 by using cos's antitoneness
  have h₆ (x : ℕ) : 0 < 2 * cos (π / 4 * (1 + f x)) := by
    suffices 0 < cos (π / 4 * (1 + f x)) by linarith
    rw [← cos_pi_div_two]
    apply Real.strictAntiOn_cos
    . and_intros
      . suffices 0 ≤ 1 + f x by positivity
        linarith [h₅ x]
      . nth_rw 2 [show π = π / 4 * 4 by ring]
        gcongr
        linarith [h₅ x]
    . and_intros <;> linarith [pi_pos]
    . suffices π / 2 * f x < π / 2 * 1 by linarith
      gcongr
      linarith [h₅ x]
  have h₇ (x : ℕ) : 2 * cos (π / 4 * (1 + f x)) < 1 := by
    suffices cos (π / 4 * (1 + f x)) < 1 / 2 by linarith
    rw [← cos_pi_div_three]
    apply Real.strictAntiOn_cos
    . and_intros <;> linarith [pi_pos]
    . and_intros
      . suffices 0 ≤ π / 4 * f x by linarith [pi_pos]
        have := (h₅ x).left
        positivity
      . suffices π / 4 * f x ≤ π / 4 * 3 by linarith [pi_pos]
        gcongr
        linarith [h₅ x]
    . suffices π * (1 / 3) < π * f x by linarith
      gcongr
      linarith [h₅ x]
  -- we can finally prove the goal, last bound on cos proves we only need to prove  sin (π / 4 * (1 - f x)) <  (π / 4 * (1 - f x)), and sin x < x happens for positive x, so we just prove that.
  rintro x
  rw [h₃]
  calc
    _ < sin (π / 4 * (1 - f x)) := by
      apply mul_lt_of_lt_one_left
      . apply Real.sin_pos_of_pos_of_lt_pi
        . suffices π / 4 * f x < π / 4 * 1 by linarith
          gcongr
          linarith [h₅ x]
        . suffices π / 4 * 0 ≤ π / 4 * f x by linarith [pi_pos]
          gcongr
          linarith [h₅ x]
      . exact h₇ x
    _ < _ := by
      apply Real.sin_lt
      suffices π / 4 * f x < π / 4 * 1 by linarith
      gcongr
      linarith [h₅ x]