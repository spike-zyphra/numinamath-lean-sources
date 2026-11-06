import Mathlib
open Nat Finset Function
noncomputable section

/-Let $a_{1}, a_{2}, \ldots$ be an infinite sequence of positive integers such that for integers $n>2, a_{n}=$ $3 a_{n-1}-2 a_{n-2}$. How many such sequences $\left\{a_{n}\right\}$ are there such that $a_{2010} \leq 2^{2012}$ ?-/
theorem number_theory_608763 :
    (Finset.sum (range 9) fun a ↦ (2^2012 - a * 2^2009 + a : ℕ)) = 36 * 2^2009 + 36 := by
  -- Step $1$: Split the sum.
  have h_split_sum : (Finset.sum (range 9) fun a ↦ (2^2012 - a * 2^2009 + a : ℕ)) =
      Finset.sum (range 9) (fun _ ↦ 2^2012) - Finset.sum (range 9) (fun a ↦ a * 2^2009) + Finset.sum (range 9) id := by
    have h_rewrite : (fun a ↦ (2^2012 - a * 2^2009 + a : ℕ)) = (fun a ↦ (2^2012 - a * 2^2009) + a) := by
      ring
    rw [h_rewrite]
    rw [Finset.sum_add_distrib]
    have h_sub : Finset.sum (Finset.range 9) (fun x ↦ (2^2012 - x * 2^2009 : ℕ)) =
      Finset.sum (Finset.range 9) (fun _ ↦ 2^2012) - Finset.sum (Finset.range 9) (fun x ↦ x * 2^2009) := by
      rw [Finset.sum_tsub_distrib]
      intros x hx
      have : x * 2 ^ 2009 ≤ 2 ^ 2012 := by
        have h₁: x < 9 := Finset.mem_range.mp hx
        have h₂: 2 ^ 2012 = 8 * 2 ^ 2009 := by ring
        have h₃: 0 < 2 ^ 2009 := by omega
        omega
      exact this
    rw [h_sub]
    have : Finset.sum (Finset.range 9) (fun x ↦ x) = (Finset.range 9).sum id := by
      rw [Finset.sum_congr]
      · rfl
      · intros x _
        rfl
    rw [this]
  -- Step $2$: Compute the first term.
  have h_const_sum : Finset.sum (range 9) (fun _ ↦ 2^2012) = 9 * 2^2012 := by
    rw [sum_const, card_range, nsmul_eq_mul]
    norm_num
  -- Step $3$: Compute the second term.
  have h_linear_sum : Finset.sum (range 9) (fun a ↦ a * 2^2009) = 36 * 2^2009 := by
    have h_rewrite : (fun a ↦ a * 2^2009) = (fun a ↦ 2^2009 * a) := by
      ext a
      rw [mul_comm]
    rw [h_rewrite]
    rw [← Finset.mul_sum, sum_range_id]
    norm_num
  -- Step $4$: Compute the third term.
  have h_index_sum : Finset.sum (range 9) id = 36 := by
    have h_id : (id : ℕ → ℕ) = fun i => i := by
      ext i
      rfl
    rw [h_id]
    rw [Finset.sum_range_id]
  -- Step $5$: Substitute and simplify.
  have h_result : 9 * 2^2012 - 36 * 2^2009 + 36 = 36 * 2^2009 + 36 := by
    have : 9 * 2^2012 = 72 * 2^2009 := by ring
    rw [this]
    ring_nf
  rw [h_split_sum, h_const_sum, h_linear_sum, h_index_sum, h_result]
