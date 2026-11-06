import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find, with proof, all functions  $f$  mapping integers to integers with the property that
for all integers  $m,n$ ,   $$ f(m)+f(n)= \max\left(f(m+n),f(m-n)\right). $$  -/
theorem number_theory_8648 {f : ℤ → ℤ} (hf : ∀ m n, f m + f n = max (f (m + n)) (f (m - n)))
    (x : ℤ) : f x = f 1 * |x| := by
  -- We can calculate f(0)=0 by substituting m=n=0.
  have hf00 := hf 0 0
  simp at hf00
  have hfmm (m : ℤ) := hf m m
  have hfmnegm (m : ℤ) := hf m (-m)
  -- We can deduce that f(m) is non-negative.
  have hfnonneg (m : ℤ) : 0 ≤ f m := by
    suffices 0 ≤ f m + f m by linarith
    rw [hfmm, sub_self, hf00]
    exact Int.le_max_right (f (m + m)) 0
  -- We can deduce that f(m) is an even function.
  have hfeven (m : ℤ) : f m = f (- m) := by
    specialize hfmm m
    specialize hfmnegm m
    rw [sub_self] at hfmm
    rw [add_neg_cancel, sub_neg_eq_add, max_comm] at hfmnegm
    linear_combination hfmm - hfmnegm
  -- Prove that f(n)=nf(1) by induction where n is positive.
  have hf_of_pos {n : ℤ} (hnpos : 0 < n) : f n = f 1 * n := by
    suffices ∀ n : ℕ, f n = f 1 * n by
      convert this n.natAbs
      all_goals rw [Int.natCast_natAbs, abs_of_pos hnpos]
    intro n
    induction' n using Nat.strongRecOn with n ih
    rcases le_or_lt n 1
    . interval_cases n
      . simp [hf00]
      . simp
    have hfn_sub_one := hf ↑(n - 1) 1
    rw [show ↑(n - 1) + 1 = (n : ℤ) by omega, show ↑(n - 1) - 1 = (↑(n - 2) : ℤ) by omega,
      ih _ (show n - 1 < n by omega), ih _ (show n - 2 < n by omega)] at hfn_sub_one
    by_cases hf1 : f 1 = 0
    . simp [hf1] at hfn_sub_one
      have := hfnonneg n
      rw [← max_eq_left_iff] at this
      rw [← this] at hfn_sub_one
      rw [hf1, zero_mul]
      simp at hfn_sub_one
      specialize hfnonneg ↑n
      linarith [hfnonneg, hfn_sub_one]
    change _ ≠ _ at hf1
    rcases le_or_lt (f 1 * ↑(n - 2)) (f n) with hfn | hfn
    . rw [← max_eq_left_iff] at hfn
      rw [hfn] at hfn_sub_one
      rw [← hfn_sub_one]
      conv => lhs; rhs; rw [← mul_one (f 1)]
      rw [← mul_add]
      congr
      omega
    rw [max_eq_right_of_lt hfn] at hfn_sub_one
    conv at hfn_sub_one => lhs; rhs; rw [← mul_one (f 1)]
    rw [← mul_add, mul_right_inj' hf1, show ↑(n - 1) + 1 = (n : ℤ) by omega] at hfn_sub_one
    norm_cast at hfn_sub_one
    omega
  -- Finally, we draw conclusion that f(x)=f(1)|x|.
  rcases lt_trichotomy x 0 with hx | hx | hx
  . have hxneg_pos : 0 < -x := Int.neg_pos_of_neg hx
    rw [hfeven x, hf_of_pos hxneg_pos, abs_of_neg hx]
  . simp [hx, hf00]
  . rw [hf_of_pos hx, abs_of_pos hx]
