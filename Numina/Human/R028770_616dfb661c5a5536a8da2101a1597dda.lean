import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- Call a real-valued function $f$ very convex if  $$ \frac{f(x)+f(y)}{2} \geq f\left(\frac{x+y}{2}\right)+|x-y| $$  holds for all real numbers $x$ and $y$. Prove that no very convex function exists. -/
theorem inequalities_606262
    (P : (ℝ → ℝ) → Prop)
    (hP : P = λ f => ∀ x y, (f x + f y) / 2 ≥ f ((x + y) / 2) + |x - y|)
    : ¬ ∃ f, P f := by

  -- Assume that there exists a very convex function $f$.
  by_contra h
  obtain ⟨f, hf⟩ := h
  -- then ∀ x y, $$ \frac{f(x)+f(y)}{2} \geq f\left(\frac{x+y}{2}\right)+|x-y| $$ holds.
  simp [hP] at hf
  -- let x = a, y = 0, then we have $$ f(a/2)≤\frac{f(a)}{2}+f(0)/2-|a| $$.
  -- by induction, we have $$ f(a/2^{k+1})≤\frac{f(a)}{2^{k+1}}+f(0)(1-1/2^{k+1})-(k+1)|a|/2^{k} $$.
  have hk (a : ℝ) {k : ℕ} : f (a / 2 ^ (k + 1)) ≤ (f a) / 2 ^ (k + 1) + f 0 * (1 - 1 / 2 ^ (k + 1)) - (k + 1) * |a| / 2 ^ k := by
    induction k with
    | zero =>
      simp
      obtain hf := hf a 0
      simp at hf
      linarith only [hf]
    | succ k' ih =>
      obtain hf := hf (a / 2 ^ (k' + 1)) 0
      simp at hf
      calc
        _ = f (a / 2 ^ (k' + 1) / 2) := by ring_nf
        _ ≤ (f (a / 2 ^ (k' + 1)) + f 0) / 2 - |a / 2 ^ (k' + 1)| := by linarith only [hf]
        _ ≤ (f a / 2 ^ (k' + 1) + f 0 * (1 - 1 / 2 ^ (k' + 1)) - (↑k' + 1) * |a| / 2 ^ k' + f 0) / 2 - |a / 2 ^ (k' + 1)| := by rel [ih]
        _ = _ := by
          simp [mul_add, add_mul, abs_div]
          ring

  -- let x = a, y = -a, then we have $$ f(0)≤\frac{f(a)+f(-a)}{2}-|a| $$.
  -- let a = 1/2^{k+1}, then we have $$ f(0)≤\frac{f(1/2^{k+1})+f(-1/2^{k+1})}{2}-|1/2^{k+1}| $$.
  -- apply the above inequality, we have $$ f(0)≤\frac{f(1)+f(-1)}{2^{k+2}}+f(0)(1-1/2^{k+1})-(k+1)/2^{k} $$.
  have h0 {k : ℕ} : f 0 + 1 / 2 ^ k ≤ (f 1 + f (-1)) / 2 ^ (k + 2) + f 0 * (1 - 1 / 2 ^ (k + 1)) - (k + 1) / 2 ^ k := by
    obtain hf := hf (1 / 2 ^ (k + 1)) (- (1 / 2 ^ (k + 1)))
    simp only [add_neg_cancel, zero_div] at hf
    calc
      _ = f 0 + |1 / 2 ^ (k + 1) - -(1 / 2 ^ (k + 1))| := by
        rw [sub_neg_eq_add, pow_add, div_mul_eq_div_div, eq_comm]
        simp
      _ ≤  (f (1 / 2 ^ (k + 1)) + f (-(1 / 2 ^ (k + 1)))) / 2 := by exact hf
      _ = (f (1 / 2 ^ (k + 1)) + f (-1 / 2 ^ (k + 1))) / 2 := by congr; ring
      _ ≤ (((f 1) / 2 ^ (k + 1) + f 0 * (1 - 1 / 2 ^ (k + 1)) - (↑k + 1) * |1| / 2 ^ k) +
          ((f (-1)) / 2 ^ (k + 1) + f 0 * (1 - 1 / 2 ^ (k + 1)) - (↑k + 1) * |-1| / 2 ^ k)) / 2 := by rel [hk 1, hk (-1)]
      _ = _ := by simp; ring_nf

  -- therefore, we have $$ f(1)+f(-1)-2f(0)≥4(k+2) $$.
  have hsub {k : ℕ} : f 1 + f (-1) - 2 * f 0 ≥ 4 * (k + 2) := by
    calc
      f 1 + f (-1) - 2 * f 0 = ((f 1 + f (-1)) / 2 ^ (k + 2) -  (f 0) / 2 ^ (k + 1)) * 2 ^ (k + 2) := by
        rw [sub_mul, div_mul_cancel₀, pow_add, pow_add]
        · ring_nf
          congr
          simp
        · exact Ne.symm (NeZero.ne' (2 ^ (k + 2)))
      _ = ((f 1 + f (-1)) / 2 ^ (k + 2) + f 0 * (1 - 1 / 2 ^ (k + 1)) - (k + 1) / 2 ^ k -  (f 0) + (k + 1) / 2 ^ k) * 2 ^ (k + 2) := by ring
      _ ≥ (f 0 + 1 / 2 ^ k -  (f 0) + (k + 1) / 2 ^ k) * 2 ^ (k + 2) := by rel [h0]
      _ = (k + 2) / 2 ^ k * 2 ^ (k + 2) := by ring
      _ = _ := by
        rw [pow_add, ←mul_assoc, div_mul_cancel₀]
        · ring
        · exact Ne.symm (NeZero.ne' (2 ^ k))

  -- however, k is arbitrary, we can choose k such that $$ f(1)+f(-1)-2f(0)<4(k+2) $$.
  -- i.e., let k = ⌈(f(1)+f(-1)-2f(0))/4⌉, then $$ f(1)+f(-1)-2f(0)≤4k $$ and $$ f(1)+f(-1)-2f(0)>4k $$.
  let k := Nat.ceil ((f 1 + f (-1) - 2 * f 0) / 4)
  have h1 : k ≥ (f 1 + f (-1) - 2 * f 0) / 4 := by
    simp only [k]
    exact Nat.le_ceil ((f 1 + f (-1) - 2 * f 0) / 4)
  have h2 : ¬ k ≥ (f 1 + f (-1) - 2 * f 0) / 4 := by
    push_neg
    calc
      (k : ℝ) = 4 * (k + 2) / 4 - 2 := by ring
      _ ≤ (f 1 + f (-1) - 2 * f 0) / 4 - 2:= by rel [hsub]
      _ < _ := by simp

  -- which is a contradiction
  contradiction
