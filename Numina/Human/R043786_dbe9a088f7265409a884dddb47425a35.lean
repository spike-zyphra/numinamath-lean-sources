import Mathlib

/- If $n$ and $k$ are positive integers such that $5<\frac nk<6$, then what is the smallest possible value of $\frac{\mathop{\text{lcm}}[n,k]}{\gcd(n,k)}$? -/
theorem number_theory_19048 :
    IsLeast {x : ℕ | ∃ n k : ℕ, n > 0 ∧ k > 0 ∧ 5 < (n / k : ℝ) ∧ (n / k : ℝ) < 6 ∧ x = Nat.lcm n k / Nat.gcd n k} 22 := by
  constructor
  -- $22$ is such a value
  use 11
  use 2
  norm_num
  -- $22$ is the least such
  intro m min
  rcases min with ⟨n, k, hn, hk, lenk, nkle, meq⟩
  -- if $n = n' \gcd(n, k)$ and $k = k' \gcd(n, k)$ then $\lcm(n, k)/\gcd(n, k) = n'k'$
  have dvdn : n.gcd k ∣ n := by
    exact Nat.gcd_dvd_left n k
  rcases dvdn with ⟨n', neq⟩
  have dvdn : n.gcd k ∣ k := by
    exact Nat.gcd_dvd_right n k
  rcases dvdn with ⟨k', keq⟩
  have meq2 : m = n' * k' := by
    rw [meq]
    refine Nat.div_eq_of_eq_mul_right ?_ ?_
    exact Nat.gcd_pos_of_pos_left k hn
    have gleq := Nat.gcd_mul_lcm n k
    nth_rw 3 [neq] at gleq
    nth_rw 4 [keq] at gleq
    rw [mul_assoc] at gleq
    apply Nat.eq_of_mul_eq_mul_left (by exact Nat.gcd_pos_of_pos_left k hn) at gleq
    rw [gleq]
    ring
  -- $k' \geq 2$
  have kge : 2 ≤ k' := by
    by_contra contra
    rw [not_le] at contra
    interval_cases k'
    linarith
    rw [mul_one] at keq
    rw [← keq] at neq
    have nleorge : n' ≤ 5 ∨ 6 ≤ n' := by
      refine Nat.le_or_le_of_add_eq_add_pred ?_
      norm_num
      ring
    apply congrArg (fun (x : ℕ) ↦ (x : ℝ)) at neq
    simp only [Nat.cast_mul] at neq
    rcases nleorge with nle | nge
    -- if $n' \leq 5$
    have nle2 : (n' : ℝ) ≤ (5 : ℤ) := by
      exact Nat.cast_le_ofNat.mpr nle
    simp only [Int.cast_ofNat] at nle2
    rw [neq, mul_div_cancel_left₀] at lenk
    linarith
    have kgt : (0 : ℝ) < k := by
      exact Nat.cast_pos'.mpr hk
    linarith
    -- if $n' \geq 6$
    have nge2 : (6 : ℤ) ≤ (n' : ℝ) := by
      exact Nat.ofNat_le_cast.mpr nge
    simp only [Int.cast_ofNat] at nge2
    rw [neq, mul_div_cancel_left₀] at nkle
    linarith
    have kgt : (0 : ℝ) < k := by
      exact Nat.cast_pos'.mpr hk
    linarith
  -- $n' \geq 11$
  have nge : 11 ≤ n' := by
    by_contra contra
    rw [not_le] at contra
    apply Nat.le_of_lt_succ at contra
    rw [neq] at lenk
    nth_rw 2 [keq] at lenk
    simp at lenk
    have gcdne : (n.gcd k : ℝ) ≠ 0 := by
      have gcdne : n.gcd k ≠ 0 := by
        refine Nat.ne_zero_iff_zero_lt.mpr ?_
        exact Nat.gcd_pos_of_pos_left k hn
      exact Nat.cast_ne_zero.mpr gcdne
    have eq : (n.gcd k : ℝ) * (n' : ℝ) / ((n.gcd k : ℝ) * (k' : ℝ)) = (n' : ℝ) / (k' : ℝ) * ((n.gcd k : ℝ) / (n.gcd k : ℝ)) := by
      ring_nf
    rw [eq, div_self gcdne, mul_one] at lenk
    have le : (n': ℝ) / k' ≤ (n' : ℝ) / 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact Nat.ofNat_le_cast.mpr kge)
    have le2 : (n' : ℝ) / 2 ≤ 10 / 2 := by
      exact div_le_div_of_nonneg_right (by exact Nat.cast_le_ofNat.mpr contra) (by exact zero_le_two)
    norm_num at le2
    linarith
  -- so $m \geq 22$
  rw [meq2]
  show 11 * 2 ≤ n' * k'
  exact Nat.mul_le_mul nge kge