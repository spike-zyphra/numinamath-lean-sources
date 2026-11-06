import Mathlib

open Finset Real

/- Does there exist a sequence $a_{1}, a_{2}, \ldots, a_{n}, \ldots$ of positive real numbers satisfying both of the following conditions:
(i) $\sum_{i=1}^{n} a_{i} \leq n^{2}$, for every positive integer $n$;
(ii) $\sum_{i=1}^{n} \frac{1}{a_{i}} \leq 2008$, for every positive integer $n$ ? -/
theorem inequalities_606356 :
  ¬ ∃ a : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, ∑ i ∈ range n, a i ≤  n^2) ∧
      (∀ n, ∑ i ∈ range n, 1 / a i ≤ 2008) := by
  -- suppose on the contrary, such sequence exist.
  rintro ⟨a, apos, ha1, ha2⟩
  -- we prove the contradiction by showing if a satisfy ha1,
  -- then 1/a diverge.
  -- recall that harmonic mean ≤ arith mean
  have h1(n:ℕ): 2^n / ∑ i ∈ range (2^n), 1 / a (2^n+i) ≤
    (∑ i ∈ range (2^n), a (2^n+i)) / 2^n := by
    have apos': ∀i ∈ range (2^n), 0 < a (2^n+i) := fun _ _ => (apos _)
    have hn': (range (2^n)).Nonempty := by simp
    set w: ℕ → ℝ := fun _ => 1 with w_def
    have wpos: ∀i ∈ range (2^n), 0 < w i := by simp [w_def]
    have wsumpos: 0 < ∑i∈ range (2^n), w i := by
      apply Finset.sum_pos wpos hn'
    -- rewrite both sides
    have lhs: 2^n / ∑ i ∈ range (2^n), 1 / a (2^n+i) =
      (∑ i ∈ range (2^n), w i) /
        (∑ i ∈ range (2^n), (w i / a (2^n+i))) := by
      simp only [w_def, sum_const, card_range, nsmul_eq_mul,
      mul_one, Nat.cast_pow, Nat.cast_ofNat]
    have rhs: (∑ i ∈ range (2^n), a (2^n+i)) / 2^n =
      (∑ i ∈ range (2^n), w i * a (2^n+i)) /
        (∑ i ∈ range (2^n), w i) := by
      congr 1
      all_goals simp [w_def]
    rw [lhs, rhs]
    -- harmonic mean ≤ geom mean ≤ arith mean
    apply le_trans (harm_mean_le_geom_mean
      (range (2^n)) hn' w _ wpos wsumpos apos') ?_
    apply geom_mean_le_arith_mean _ _ _ ?_ wsumpos ?_
    · simp [w_def]
    · exact fun _ h => (le_of_lt (apos' _ h))
  -- mul the sum of left side to right
  have h2(n:ℕ): (∑ i ∈ range (2^n), 1 / a (2^n+i)) *
    (∑ i ∈ range (2^n), a (2^n+i)) ≥ 2^(2*n) := by
    have{x y: ℝ}(hx: 0 < x)(h: (2:ℝ)^n / x ≤ y / 2^n):
      x*y ≥ 2^(2*n) := by
      have hh1: x * (2^n/x) ≤ x * (y/2^n) := by
        exact (mul_le_mul_iff_of_pos_left hx).mpr h
      rw [mul_div_cancel₀ _ hx.ne', mul_div_assoc'] at hh1
      have hh2: 0 < (2:ℝ)^n := by simp
      have hh3: (2:ℝ)^(2*n) = 2^n * 2^n := by
        rw [mul_comm 2 n, pow_mul, pow_two]
      have hh4: x*y = (x*y/2^n)*2^n := by
        exact (div_mul_cancel_of_invertible _ _).symm
      rw [hh3, hh4]
      exact (mul_le_mul_iff_of_pos_right hh2).mpr hh1
    apply this ?_ (h1 n)
    apply Finset.sum_pos ?_ ?_
    · intro _ _
      apply div_pos (by norm_num) (apos _)
    · simp
  -- by problem statement, sum a (2^n+i) ≤ 4 x 2^(2n)
  have h3(n:ℕ): ∑ i ∈ range (2^n), a (2^n+i) ≤ 4 * 2^(2*n) := by
    specialize ha1 (2^n + 2^n)
    rw [Finset.sum_range_add, ← two_mul] at ha1
    push_cast at ha1
    rw [mul_pow, ← pow_mul, mul_comm n 2] at ha1
    norm_num at ha1
    apply le_trans ?_ ha1
    simp only [le_add_iff_nonneg_left]
    apply Finset.sum_nonneg
    intro _ _
    apply le_of_lt (apos _)
  -- therefore sum 1 / a_{2^n+i} ≥ 1/4
  replace h2(n:ℕ): ∑ i ∈ range (2^n), 1 / a (2^n + i) ≥ 1/4 := by
    have{x y z: ℝ}(ypos: 0 < y)
      (hx1: x*y ≥ z)(hx2: y ≤ 4*z): x ≥ 1/4 := by
      have hh1: y ≤ y * (4*x) := calc
        y ≤ 4*z := hx2
        _ ≤ 4*(x*y) := (mul_le_mul_left (by norm_num)).mpr hx1
        _ = _ := by ring
      have hh2: 1 ≤ 4*x := one_le_of_le_mul_left₀ ypos hh1
      linarith [hh2]
    apply this ?_ (h2 n) (h3 n)
    apply Finset.sum_pos ?_ ?_
    · intro _ _; apply apos
    · simp
  -- notice that a0+a1+a2+... = a0 + (a1) + (a2+a3) + (a4+a5+a6+a7) + ...
  have h4{n:ℕ}(hn: n ≥ 1): ∑ i ∈ range (2^n), 1 / a i =
    1 / a 0 + ∑ k ∈ range n, (∑ i ∈ range (2^k), 1 / a (2^k+i)) := by
    induction' n,hn using Nat.le_induction with n hn ih
    · simp [Finset.sum_range_succ]
    · rw [pow_succ, mul_two, Finset.sum_range_add, ih]
      rw [add_assoc]; congr 1
      rw [Finset.sum_range_succ]
  -- therefore sum to 2^n ≥ 1/a0 + sum to n x (1/4) ≥ n/4
  replace h4{n:ℕ}(hn: n ≥ 1): ∑ i ∈ range (2^n), 1 / a i ≥ n/4 := by
    have hh1: ∑ k ∈ range n, (∑ i ∈ range (2^k), 1 / a (2^k+i)) ≥
      ∑ k ∈ range n, 1/4 := by
      apply Finset.sum_le_sum
      exact fun _ _ => (h2 _)
    simp only [sum_const, card_range, nsmul_eq_mul] at hh1
    have hh2: 1 / a 0 ≥ 0 := by
      apply div_nonneg (by norm_num) ?_
      apply le_of_lt (apos 0)
    rw [h4 hn]
    linarith [hh1, hh2]
  -- but ha2 says the sum converge, thus contradiction.
  have not_ha2: ∑ i ∈ range (2^(4*2008+1)), 1 / a i > 2008 := by
    have: 4*2008+1 ≥ 1 := by norm_num
    replace := h4 this
    apply lt_of_lt_of_le ?_ this
    norm_num
  absurd not_ha2
  push_neg
  apply ha2