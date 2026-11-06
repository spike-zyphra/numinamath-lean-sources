import Mathlib
import Aesop

open BigOperators Real Topology Rat

/- If  $n$  is an integer, then find all values of  $n$  for which  $\sqrt{n}+\sqrt{n+2005}$  is an integer as well.-/
theorem number_theory_8718 {n : ℤ} (hnnonneg : 0 ≤ n) :
    (∃ m : ℤ, √n + √(n + 2005) = m) ↔ n = 198^2 ∨ n = 1002^2 := by
  have hn_real_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast hnnonneg
  have divisors2005 : Nat.divisors 2005 = {1, 5, 401, 2005} := by native_decide
  constructor
  rintro ⟨m, hm⟩
  have hmnonneg : 0 ≤ (m : ℝ) := by
    rw [← hm]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmpos : 0 < (m : ℝ) := by
    rw [← hm]
    suffices 0 < √(n + 2005) by linarith [Real.sqrt_nonneg n]
    rw [Real.sqrt_pos]
    linarith
  -- √(n + 2005) - √n is rational.
  have sqrt_sub_sqrt_eq_ratCast : ∃ m : ℚ, √(n + 2005) - √n = m := by
    use 2005 / m
    field_simp [← hm]
    ring_nf
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by assumption), add_sub_cancel_right]
  -- If √n is rational then it is an integer.
  have eq_intCast_of_eq_ratCast {x : ℤ} (hxnonneg : 0 ≤ (x : ℝ)) : (∃ a : ℚ, √x = a) → (∃ b : ℤ, √x = b) := by
    rintro ⟨a, hma⟩
    have hanonneg : 0 ≤ (a : ℝ) := by rw [← hma]; exact Real.sqrt_nonneg _
    use a.num
    apply_fun (· ^ 2) at hma
    rw [Real.sq_sqrt hxnonneg] at hma
    rw [hma, Real.sqrt_sq hanonneg]
    rw [← Rat.num_div_den a] at hma
    field_simp at hma
    have : (a.den^2 : ℤ) ∣ (a.num^2) := by
      use x
      rify
      linear_combination -hma
    have : a.den ∣ a.num.natAbs^2 := by
      apply Nat.dvd_of_pow_dvd (show 1 ≤ 2 by norm_num)
      zify
      rwa [sq_abs]
    have : (a.den : ℤ) ∣ a.num := by
      zify at this
      rw [sq_abs, pow_two] at this
      apply Int.dvd_of_dvd_mul_left_of_gcd_one this
      rw [Int.gcd, ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm]
      exact a.reduced
    have : a.den = 1 := by
      apply Nat.eq_one_of_dvd_coprimes a.reduced
      . zify; rwa [dvd_abs]
      exact Nat.dvd_refl _
    nth_rw 1 [← Rat.num_div_den a]
    simp [this]
  -- √n and √(n + 2005) are integers.
  have : (∃ a : ℤ, √n = a) ∧ (∃ b : ℤ, √(n + 2005) = b) := by
    rw [show ↑n + (2005 : ℝ) = ↑(n + 2005) by simp]
    obtain ⟨r, hr⟩ := sqrt_sub_sqrt_eq_ratCast
    constructor
    apply eq_intCast_of_eq_ratCast
    . assumption
    . use (m - r) / 2
      field_simp [← hm, ← hr]
      ring
    apply eq_intCast_of_eq_ratCast
    . push_cast; linarith
    . use (m + r) / 2
      field_simp [← hm, ← hr]
      ring
  -- Let \( \sqrt{n} = a \) and \( \sqrt{n+2005} = b \), where \( a \) and \( b \) are integers.
  rcases this with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  -- Need nonneg condition to calc |b+a| = b+a.
  have add_ab_nonneg: 0 ≤ b + a := by
    rify
    convert hmnonneg
    rw [← hm, ← ha, ← hb, add_comm]
  -- Need positive condition to calc (b^2-a^2)/(b+a)=b-a.
  have add_ab_pos : 0 < b + a := by
    rify
    convert hmpos
    rw [← hm, ← ha, ← hb, add_comm]
  -- Then:
  --  \[
  --  b^2 - a^2 = 2005
  --  \]
  have sq_sub_sq_eq : b^2 - a^2 = 2005 := by
    rify
    rw [← ha, ← hb, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  -- Using the difference of squares, we get:
  --  \[
  --  (b-a)(b+a) = 2005
  --  \]
  have add_ab_dvd : b + a  ∣ 2005 := by
    rw [← sq_sub_sq_eq, sq_sub_sq]
    exact Int.dvd_mul_right ..
  -- For \( a \) and \( b \) to be integers, \( k \) must be a divisor of 2005.
  have add_ab_mem_divisors : (b + a).natAbs ∈ Nat.divisors 2005 := by
    rw [Nat.mem_divisors]
    refine ⟨?_, by norm_num⟩
    zify
    rw [abs_of_nonneg add_ab_nonneg]
    exact add_ab_dvd
  have sub_ab_eq : b - a = 2005 / (b + a) := by
    rw [← sq_sub_sq_eq, sq_sub_sq, mul_comm, Int.mul_ediv_cancel _ add_ab_pos.ne']
  -- The divisors of 2005 are \( 1, 5, 401, 2005 \).
  simp [divisors2005] at add_ab_mem_divisors
  zify at add_ab_mem_divisors
  rw [abs_of_nonneg add_ab_nonneg] at add_ab_mem_divisors
  have hanonneg : 0 ≤ a := by rify; rw [← ha]; exact Real.sqrt_nonneg _
  rcases add_ab_mem_divisors with h | h | h | h
  any_goals rw [h] at sub_ab_eq
  -- Checking each divisor:
  -- - For \( k = 1 \):
  -- This system has no integer solutions.
  . have : a < 0 := by omega
    linarith
  -- - For \( k = 5 \):
  -- This system has no integer solutions.
  . have : a < 0 := by omega
    linarith
  -- - For \( k = 401 \):
  -- The solution is n=198^2.
  . have : a = 198 := by omega
    left
    rify
    rw [← Real.sq_sqrt (x := n) (by linarith), ha, this]
    rfl
  -- - For \( k = 401 \):
  -- The solution is n=1002^2.
  . have : a = 1002 := by omega
    right
    rify
    rw [← Real.sq_sqrt (x := n) (by linarith), ha, this]
    rfl
  -- Verify that n=198^2 and n=1002^2 are solutions.
  intro hn
  rcases hn with hn | hn
  -- n=198
  . use 401
    rw [hn, Int.cast_pow, Real.sqrt_sq (by norm_num), Int.cast_ofNat, Int.cast_ofNat,
      show 198^2+2005 = (203 : ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  -- n=1002
  . use 2005
    rw [hn, Int.cast_pow, Real.sqrt_sq (by norm_num), Int.cast_ofNat, Int.cast_ofNat,
      show 1002^2+2005=(1003 : ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
