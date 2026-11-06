import Mathlib

open Finset

/- For $2 k$ real numbers $a_{1}, a_{2}, \ldots, a_{k}, b_{1}, b_{2}, \ldots, b_{k}$ define the sequence of numbers $X_{n}$ by

$$
X_{n}=\sum_{i=1}^{k}\left[a_{i} n+b_{i}\right] \quad(n=1,2, \ldots)
$$

If the sequence $X_{n}$ forms an arithmetic progression, show that $\sum_{i=1}^{k} a_{i}$ must be an integer. Here $[r]$ denotes the greatest integer less than or equal to $r$. -/
theorem number_theory_605479 (k : ℕ) (a b : Fin k → ℝ)
    (h : ∃ d, ∀ n : ℕ, ∑ i, ⌊a i * n + b i⌋ = ∑ i, ⌊a i * 0 + b i⌋ + d * n) :
    ∃ m : ℤ, ∑ i, a i = m := by
  -- If k = 0 then the conclusion is trivial
  rcases k.eq_zero_or_pos with hk | hk; · subst hk; use 0; simp
  -- Define X (0-indexed), A and B of the informal solution
  let X : ℕ → ℤ := fun n ↦ ∑ i, ⌊a i * n + b i⌋
  rw [show (0 : ℝ) = (0 : ℕ) by norm_cast] at h
  change ∃ d, ∀ n, X n = X 0 + d * n at h
  set A := ∑ i, a i
  let B := ∑ i, b i
  have AnB : ∀ n, A * n + B = ∑ i, (a i * n + b i) := fun n ↦ by
    unfold A B; rw [sum_mul, sum_add_distrib]
  -- For all $n$, $A n + B - k < X_n ≤ A n + B$ (using that $0 < k$ for the $<$)
  have X_bounds : ∀ (n : ℕ), (X n : ℝ) ∈ Set.Ioc (A * n + B - k) (A * n + B) := fun n ↦ by
    simp_rw [X, Int.cast_sum, AnB]
    constructor
    · simp_rw [show k = ∑ i : Fin k, 1 by simp, Nat.cast_sum, ← sum_sub_distrib, Nat.cast_one]
      exact sum_lt_sum_of_nonempty ⟨⟨0, hk⟩, mem_univ _⟩ fun i _ ↦ Int.sub_one_lt_floor _
    · exact sum_le_sum fun i _ ↦ Int.floor_le _
  -- Obtain the common difference $d$ of the arithmetic progression
  obtain ⟨d, hd⟩ := h
  -- For all $n$, $A n + (B - X 0) - k < n d ≤ A n + (B - X 0)$
  have nd_bounds : ∀ (n : ℕ),
      (n * d : ℝ) ∈ Set.Ioc (A * n + (B - X 0) - k) (A * n + (B - X 0)) := fun n ↦ by
    have := X_bounds n
    rw [hd n, Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_comm (d : ℝ)] at this
    rw [Set.mem_Ioc] at this ⊢
    constructor
    · replace this := this.1
      rwa [← add_sub_assoc, sub_right_comm, sub_lt_iff_lt_add, add_comm _ (X 0 : ℝ)]
    · replace this := this.2
      rwa [← add_sub_assoc, le_sub_iff_add_le, add_comm _ (X 0 : ℝ)]
  -- `X_bounds 0` gives $0 ≤ B - X_0 < k$. For all $n$, $A n - k < n d < A n + k$
  replace nd_bounds : ∀ (n : ℕ), (n * d : ℝ) ∈ Set.Ioo (A * n - k) (A * n + k) := fun n ↦ by
    obtain ⟨lb, ub⟩ := X_bounds 0
    rw [Nat.cast_zero, mul_zero, zero_add] at lb ub
    refine ⟨lt_of_le_of_lt ?_ (nd_bounds n).1, (nd_bounds n).2.trans_lt ?_⟩
    · rwa [sub_le_sub_iff_right, le_add_iff_nonneg_right, sub_nonneg]
    · rwa [add_lt_add_iff_left, sub_lt_comm]
  -- or $|A - d| < k / n$
  have diff_bounds : ∀ (n : ℕ), 0 < n → |A - d| < k / n := fun n hn ↦ by
    rw [abs_sub_lt_iff, lt_div_iff₀ (Nat.cast_pos'.mpr hn), lt_div_iff₀ (Nat.cast_pos'.mpr hn),
      sub_mul, sub_mul, sub_lt_comm]
    nth_rw 2 [sub_lt_iff_lt_add']
    rw [← Set.mem_Ioo, mul_comm (d : ℝ)]
    exact nd_bounds n
  -- Since $n$ was arbitrary, $A = d$, an integer. This completes the proof
  use d
  suffices |A - d| = 0 by rwa [abs_eq_zero, sub_eq_zero] at this
  apply eq_of_ge_of_not_gt (abs_nonneg (A - d)); by_contra h
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt h
  specialize diff_bounds ((n₀ + 1) * k) (Nat.succ_mul_pos n₀ hk)
  rw [Nat.cast_mul, div_mul_cancel_right₀ (by positivity), inv_eq_one_div, Nat.cast_add,
    Nat.cast_one] at diff_bounds
  exact lt_asymm hn₀ diff_bounds