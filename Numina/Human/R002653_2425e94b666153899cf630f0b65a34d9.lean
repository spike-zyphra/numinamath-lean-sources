import Mathlib
import Mathlib.Analysis.SpecificLimits.Normed
open Real
open Nat

/-
Two real, infinite geometric series each have a sum of 1 and have the same second term.
The third term of one of the series is $\frac{1}{8}$,
and the second term of both series can be written in the form $\frac{\sqrt{m}-n}{p}$,
where $m, n$, and $p$ are positive integers and $m$ is not divisible by the square of any prime,
and $m$ is not 1. Find $100m + 10n + p$
-/


theorem AIME_Algebra_720
  (s1 s2 : ℕ → ℝ)
  (hs1 : Summable s1)
  (hs2 : Summable s2)
  (hs1D : ∃ a r, s1 = fun n => a * (r ^ n))
  (hs2D : ∃ a r, s2 = fun n => a * (r ^ n))
  (hs1Eq : ∑' n, s1 n = 1)
  (hs2Eq : ∑' n, s2 n = 1)
  (hs1_2 : s1 2 = 1 / 8)
  (hEq : s1 1 = s2 1)
  (m n p : ℕ)
  (hm : m ≠ 1)
  (hp : p ≠ 0)
  (hvm : ∀ v, v.Prime → ¬ (v^2 ∣ m))
  (hmnp : (s1 1 = (√(m : ℝ) - n) / p))
  : 100 * m + 10 * n + p = 518 := by

/-
$s1$ is the series whose third term is $\frac{1}{8}$
$a1$ is the first term of $s1$
$r1$ is the common ratio of $s1$
$a2$ is the first term of $s2$
$r2$ is the common ratio of $s2$
-/
  set x := s1 1
  have hx : x = s1 1 := rfl
  let ⟨a1, r1, h1⟩ := hs1D
  let ⟨a2, r2, h2⟩ := hs2D

/-
First term of both series can't be zero, cause that leads to a sum of zero.
-/
  have a1_ne_0 : a1 ≠ 0 := by
    by_contra ha
    conv at hs1Eq =>
      arg 1
      arg 1
      rw [((Set.eqOn_univ (fun n ↦ s1 n) (fun n ↦ 0)).mp (fun x hx =>
        (by
          whnf
          rw [h1, ha]
          simp only [zero_mul]
          : s1 x = 0)))]
    rw [tsum_zero] at hs1Eq
    exact zero_ne_one hs1Eq
  have a2_ne_0 : a2 ≠ 0 := by
    by_contra ha
    conv at hs2Eq =>
      arg 1
      arg 1
      rw [((Set.eqOn_univ (fun n ↦ s2 n) (fun n ↦ 0)).mp (fun x hx =>
        (by
          whnf
          rw [h2, ha]
          simp only [zero_mul]
          : s2 x = 0)))]
    rw [tsum_zero] at hs2Eq
    exact zero_ne_one hs2Eq


/-
Prove that each term is a multiple of the previous term by the common ratio.
-/
  have hP1 n : s1 (n + 1) = (s1 n) * r1 := by
    rw [h1]
    simp only
    rw [pow_add, pow_one, mul_assoc]

  have hQ1 n (hn : s1 n ≠ 0) : r1 = (s1 (n + 1)) / s1 n := by
    rw [hP1]
    exact Eq.symm (mul_div_cancel_left₀ r1 hn)

  have hP2 n : s2 (n + 1) = (s2 n) * r2 := by
    rw [h2]
    simp only
    rw [pow_add, pow_one, mul_assoc]

  have hQ2 n (hn : s2 n ≠ 0) : r2 = (s2 (n + 1)) / s2 n := by
    rw [hP2]
    exact Eq.symm (mul_div_cancel_left₀ r2 hn)

/-
Prove that the common ratio of $s1$ can't be zero.
Because it's third term is not zero.
-/
  have r1_ne_0 : r1 ≠ 0 := by
    by_contra hr1
    rw [h1, hr1] at hs1_2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_div,
      zero_eq_inv, OfNat.zero_ne_ofNat] at hs1_2

/-
Prove that every term in s1 can't be zero.
Beacse both of it's first term and common ratio is none zero.
-/
  have s1_ne_0 n : s1 n ≠ 0 := by
    rw [h1]
    have : r1 ^ n ≠ 0 := by exact pow_ne_zero n r1_ne_0
    exact mul_ne_zero a1_ne_0 this

  have s10_eq_a1 : s1 0 = a1 := by
    rw [h1]
    simp only
    simp only [pow_zero, mul_one]

  have hr1 : r1 = 1 / (8 * x) := by
    rw [hQ1 1 (s1_ne_0 1)]
    have : 1 + 1 = 2 := by exact rfl
    rw [this, hs1_2, div_div]

/-
The third term of $s1$ is $\frac{1}{8}$
The second term of $s1$ is $x$
So the first term of $s1$ is $8x^2$
-/
  have ha1 : a1 = 8 * x * x := by
    suffices h : s1 2 = 1 / 8 from by
      have : 2 = 0 + 1 + 1 := by rfl
      rw [this, hP1, hP1, h1] at h
      simp only [pow_zero, mul_one, one_div] at h
      rw [hr1] at h
      apply_fun (·* (8 * x)) at h
      rw [mul_assoc _ _ (8 * x)] at h
      have  : (1 / (8 * x)) * (8 * x) = 1 := by
        refine one_div_mul_cancel ?_
        simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
        have : x ≠ 0 := by rw [hx]; exact s1_ne_0 1
        simp only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
        exact this
      rw [this, mul_one] at h
      apply_fun (·* (8 * x)) at h
      rw [mul_assoc, this, mul_one] at h
      simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        IsUnit.inv_mul_cancel_left] at h
      rw [mul_comm] at h
      exact h
    exact hs1_2
  rw [h1] at hs1

/-
$s1$ is summable, so $|r1| < 1$
-/
  let s := fun n => r1 ^ n
  have hSS : Summable s := (summable_mul_left_iff a1_ne_0).mp hs1
  have r1_norm : ‖r1‖ < 1 := summable_geometric_iff_norm_lt_one.mp hSS

/-
By the sum equation of geometric series
We have $\frac{8x^2}{1 - \frac{1}{8x}} = 1$
-/
  have e1: 8 * x * x * (1 - 1 / (8 * x))⁻¹ = 1 := by
    rw [h1] at hs1Eq
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one] at hs1Eq
    rw [hr1, ha1] at hs1Eq
    exact hs1Eq
    exact r1_norm

/-
$x$ can't be zero, since every term in s1 is nonzero
-/
  have x_ne_0: x ≠ 0 := by unfold x; exact s1_ne_0 1

/-
Translate the equation of $x$ to $(4x - 1)(16x^2 + 4x - 1)=0$
-/
  have : (4 * x - 1) * (16 * x * x + 4 * x - 1) = 0 := by
    apply_fun (· * (1 - 1 / (8 * x))) at e1
    rw [mul_assoc] at e1
    have : ((1 - 1 / (8 * x))⁻¹ * (1 - 1 / (8 * x))) = 1 := by
      refine IsUnit.inv_mul_cancel ?_
      have x8_ne_1: 8 * x ≠ 1 := by
        by_contra h
        apply_fun ((1/8) *·) at h
        rw [← mul_assoc] at h
        ring_nf at h
        rw [h] at hr1
        ring_nf at hr1
        rw [hr1] at r1_norm
        rw [norm_one, lt_self_iff_false] at r1_norm
        exact r1_norm
/-
Prove that $1 - \frac{1}{8} ≠ 0$, so we can multiply it to both side of the equation
-/
      have : (1 - 1 / (8 * x)) ≠ 0 := by
        by_contra h
        apply_fun (· + (1 / (8 * x))) at h
        rw [sub_add] at h
        rw [sub_self, sub_zero, zero_add] at h
        apply_fun (· * (8 * x)) at h
        have : 8 * x ≠ 0 := by
          unfold x;
          by_contra h;
          apply_fun ((1/8) *·) at h
          rw [← mul_assoc] at h
          ring_nf at h
          exact s1_ne_0 1 h
        rw [one_div_mul_cancel this, one_mul] at h
        exact x8_ne_1 h
      exact Ne.isUnit this
    rw [this] at e1
    apply_fun (x * ·) at e1
    ring_nf at e1
    have : x * x⁻¹ = 1 := by
      exact mul_inv_cancel₀ (s1_ne_0 1)
    rw [this] at e1
    apply_fun (. - (x + 1 * (-1 / 8))) at e1
    ring_nf at e1
    apply_fun (. * 8) at e1
    group at e1
    have : 1 - x * 8 + x ^ 3 * 64 = (4 * x - 1) * (16 * x * x + 4 * x - 1) := by linarith
    rw [← this]
    exact e1

/-
Now we know that either $4x - 1=0$ or $16x^2 + 4x -1=0$
-/
  have : (4 * x - 1) = 0 ∨ (16 * x * x + 4 * x - 1) = 0 := by
    exact mul_eq_zero.mp this

  cases' this with h h
/-
When $4x - 1=0$
-/
  . have : x = 1/4 := by linarith
    rw [this] at hmnp
    have (m n p : ℕ) (hmN1 : m ≠ 1) (hP : p ≠ 0) (hmp : ∀ v, v.Prime → ¬ (v^2 ∣ m))
      (h : 1 / 4 = (√(m : ℝ) - n) / p) : False := by
      apply_fun (· * 4) at h
      rw [div_mul, div_self, one_div_one] at h
      apply_fun (· * ↑p) at h
      rw [one_mul, mul_assoc, mul_comm 4, ← mul_assoc, div_mul, div_self, div_one] at h
      have hIm: Irrational √m := by
        refine irrational_sqrt_natCast_iff.mpr ?_
        by_contra hm
        contrapose hmp
        push_neg
        obtain ⟨s, hs⟩ := hm
        have : s ≠ 1 := by
          by_contra h
          rw [h, one_mul] at hs
          exact hmN1 hs
        obtain ⟨p, ⟨hp, hd⟩⟩ := Nat.exists_prime_and_dvd this
        use p
        constructor
        . exact hp
        . rw [hs, ← pow_two]
          exact pow_dvd_pow_of_dvd hd 2
      have : Irrational ((√↑m - ↑n) * 4) := by
        have i1: (√↑m - ↑n) * 4 = (√↑m - ↑n) * (4 : ℚ) := rfl
        have i2: (√↑m - ↑n) = √↑m  - ((↑n : ℚ): ℝ) := rfl
        rw [i1, irrational_mul_rat_iff, i2, irrational_sub_rat_iff]
        constructor
        . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
        . exact hIm
      rw [← h] at this
      exact (not_irrational p) this
      exact cast_ne_zero.mpr hP
      exact Ne.symm (NeZero.ne' 4)
/-
$\frac{1}{4} = \frac{\sqrt{m} - n}{p}$, by analyzing rationality, a contradiction is derived.
-/
    exact (this m n p hm hp hvm hmnp).elim

/-
Otherwise $16x^2 + 4x - 1 = 0$
-/
  . have : 16 * x * x + 4 * x - 1 = 16 * (x * x) + 4 * x + (- 1) := by linarith
    rw [this] at h
    let s := √(discrim (16 : ℝ) 4 (-1))
    have hs : s = √(discrim 16 4 (-1)) := rfl
    have hd : discrim (16 : ℝ) 4 (-1) = 80 := by unfold discrim; linarith
    have hsv : s = √80 := by unfold s;rw [hd];
    have hds : discrim (16 : ℝ) 4 (-1) = s * s := by rw [hd, hsv, mul_self_sqrt];simp only [ofNat_nonneg]
    rw [quadratic_eq_zero_iff _ hds x] at h
/-
There are two roots for it
-/
    cases' h with hx hx
    . rw [hsv] at hx
      rw [(by
          rw [(by
            rw [(by rfl: (16 * 5) = (((16 : ℕ) : ℝ) * ((5 : ℕ) : ℝ)))]
            rw [(by rfl: (80) = ((80 : ℕ) : ℝ))]
            rw [← cast_mul]
            : (80:ℝ) = 16 * 5)]
          rw [Real.sqrt_mul]
          simp only [mul_eq_mul_right_iff, ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_false]
          refine Real.sqrt_eq_cases.mpr ?_
          left
          constructor
          . linarith
          . linarith
          . linarith
        : (√80 : ℝ) = (4 * √5))] at hx
      rw [(by
        linarith
        : (-4 + 4 * √5) / (2 * 16) = (√5 - 1) / 8)] at hx
/-
One of them is $\frac{\sqrt {5} - 1}{8}$, by analyzing rationality, that give use the unique solutions for m, n and p
$m=5,n=1,p=8$
-/
      have (m n p : ℕ) (hp : p ≠ 0) (hm : ∀ v, v.Prime → ¬ (v^2 ∣ m))
        (hEq : (√5 - 1) / 8 = (√(m : ℝ) - n) / p) : m = 5 ∧ n = 1 ∧ p = 8 := by
/-
Plugging the value of x we get $\frac{\sqrt{5} - 1}{8} = \frac{\sqrt{m}-n}{p}$
Then we have $ \sqrt{5}p - 8\sqrt{m} = p - 8n$
-/
        have e: √5  * p - 8 * √m = p - n * 8 := by
          apply_fun (·*(8 :ℝ) * p) at hEq
          have : (√↑m - ↑n) / ↑p * 8 * ↑p = (8 * (√↑m - ↑n)) / ↑p * ↑p := by group
          rw [this] at hEq
          have : (8 * (√↑m - ↑n)) / ↑p * ↑p = 8 * (√↑m - ↑n) := by
            refine IsUnit.div_mul_cancel ?_ (8 * (√↑m - ↑n))
            rw [isUnit_iff_ne_zero]
            exact cast_ne_zero.mpr hp
          rw [this] at hEq
          linarith
        by_cases h : √5  * p - 8 * √m = 0
/-
When $\sqrt{5}p - 8\sqrt{m} = 0$
-/
        . have : p = 8 * √m / √5 := by
            apply_fun (· + 8 * √m) at h
            simp only [sub_add_cancel, zero_add] at h
            apply_fun (· / √5) at h
            simp only [ne_eq, ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
              mul_div_cancel_left₀] at h
            exact h
          clear e
/-
$\sqrt{5}p = 8\sqrt{m}$
-/
          have e: p = 8 * √(m / 5) := by
            rw [Real.sqrt_div, ← mul_div_assoc]
            exact this
            exact cast_nonneg' m
          have : p = √(64 * m / 5) := by
            rw [mul_div_assoc, Real.sqrt_mul]
            have : √64 = 8 := by
              have : (64 : ℝ) = 8 * 8 := by linarith
              rw [this]
              simp only [ofNat_nonneg, Real.sqrt_mul_self]
            rw [this]
            exact e
            simp only [ofNat_nonneg]
          clear e
          have e: (p : ℝ) * p = 64 * m / 5 := by
            rw [this]
            rw [Real.mul_self_sqrt]
            apply mul_nonneg
            . apply mul_nonneg
              . simp only [ofNat_nonneg]
              . exact cast_nonneg' m
            . simp only [inv_nonneg, ofNat_nonneg]
          clear this
          apply_fun (· * 5) at e
          rw [mul_div_assoc, mul_assoc 64] at e
          clear this
          have : ((m : ℝ) / (5 : ℝ) * 5) = m := by simp only [isUnit_iff_ne_zero, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel]
          rw [this] at e
          clear this
          rw [(by rfl: 5 = ((5 : ℕ) : ℝ)), (by rfl: 64 = ((64 : ℕ) : ℝ))] at e
          rw [← cast_mul, ← cast_mul, ← cast_mul] at e
          rw [Nat.cast_inj] at e
          rw [mul_comm, mul_comm 64] at e
          have t: 5 ∣ (m * 64) := by
            use (p * p)
            exact e.symm
/-
$5$ must divides $m$
-/
          have : 5 ∣ m := by
            contrapose t
            refine Nat.Prime.not_dvd_mul ?_ t ?_
            . exact prime_five
            . exact of_decide_eq_false rfl
          clear t
          obtain ⟨k, hk⟩ := this
          rw [hk] at e
          rw [mul_assoc] at e
          rw [mul_eq_mul_left_iff] at e
          simp only [OfNat.ofNat_ne_zero, or_false] at e
          apply_fun (√·) at e
          rw [(by
            push_cast
            refine Real.sqrt_mul_self ?_
            exact cast_nonneg' p
            : √(((p * p) : ℕ) : ℝ) = (p : ℝ))] at e
          rw [(by push_cast; exact rfl : (((k * 64 : ℕ) : ℝ) = (k : ℝ) * (64 : ℝ)))] at e
          rw [Real.sqrt_mul] at e
          rw [(by
            refine Real.sqrt_eq_cases.mpr ?_
            simp only [ofNat_nonneg, and_true, OfNat.ofNat_ne_zero, and_false, or_false]
            linarith
            : √64 = 8)] at e
/-
Assuming $m = 5k$, then k must be a square number in order to to satisfy rationality.
-/
          have : IsSquare k := by
            have : ¬ Irrational (p : ℝ) := by
              exact not_irrational p
            rw [e] at this
            rw [(by
              exact rfl
             : √(k : ℝ) * (8 : ℝ) = √(k : ℝ) * ((8 : ℚ)))] at this
            rw [(by
              exact rfl
             : √(k : ℝ) = √(k : ℚ))] at this
            rw [irrational_mul_rat_iff] at this
            push_neg at this
            replace this := this (by exact Ne.symm (OfNat.zero_ne_ofNat 8))
            rw [(irrational_sqrt_ratCast_iff_of_nonneg _).not] at this
            push_neg at this
            exact Rat.isSquare_natCast_iff.mp this
            exact cast_nonneg' k
          obtain ⟨sq, hsq⟩ := this
/-
Using the requirement that $m$ is not divisible by the square of any prime,
$k$ can only be square of 1
-/
          have : sq = 1 := by
            by_contra h
            have : ∃ (min : ℕ) (h : min.Prime), min ∣ sq := by
              use sq.minFac
              refine exists_prop.mpr ?_
              constructor
              . exact Nat.minFac_prime h
              . exact minFac_dvd sq
            contrapose hm
            push_neg
            use sq.minFac
            constructor
            . exact Nat.minFac_prime h
            . rw [hk, hsq, ← pow_two]
              apply Dvd.dvd.mul_left
              refine (Nat.pow_dvd_pow_iff ?_).mpr ?_
              . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
              . exact minFac_dvd sq
/-
Thus we proved m can be only 1, by that we get $n = 10 p = 8 $
-/
          rw [hsq, this, mul_one, mul_one] at hk
          rw [hsq, this, mul_one] at e
          simp only [cast_one, Real.sqrt_one, one_mul] at e
          rw [e, hk] at hEq
          apply_fun (· * 8) at hEq
          simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            IsUnit.div_mul_cancel, cast_ofNat, sub_right_inj] at hEq
          rw [(by rfl : (8 : ℝ) = ((8 : ℕ) : ℝ)), Nat.cast_inj] at e
          rw [(by exact Eq.symm cast_one : (1 : ℝ) = ((1 : ℕ) : ℝ)), Nat.cast_inj] at hEq
          exact ⟨hk, ⟨hEq.symm, e⟩⟩
          simp only [cast_nonneg]

/-
Otherwise, rationality problem occurred
-/
        . have e1: (5 : ℝ) * ((p: ℝ) * p) - 64 * (m : ℝ)
            = (√5 * (p : ℝ) - 8 * √(m : ℝ)) * (√5 * (p : ℝ) + 8 * √(m : ℝ)) := by
            group
            rw [(by
              rw [zpow_two]
              refine Real.mul_self_sqrt ?_
              simp only [ofNat_nonneg]
              : √5 ^ (2 : ℤ) = 5)]
            rw [zpow_two √↑m]
            congr
            refine Eq.symm (Real.mul_self_sqrt ?_)
            simp only [cast_nonneg]
          apply_fun ((√5 * ↑p - 8 * √↑m)⁻¹*·) at e1
          conv at e1 =>
            right
            rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
          have hNI : ¬Irrational (√5 * ↑p) := by
            rw [(by
              group
              : √5 * ↑p = ((√5 * ↑p + 8 * √↑m) + (√5 * ↑p - 8 * √↑m)) / 2)]
            rw [←e1, e, inv_mul_eq_div]
            unfold Irrational
            push_neg
            use (((5 * (↑p * ↑p) - 64 * ↑m) / (↑p - ↑n * 8) + (↑p - ↑n * 8)) / 2 : ℚ)
            simp only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
              Rat.cast_natCast]
          have hI : Irrational (√5 * ↑p) := by
            rw [(by
              simp only [Rat.cast_natCast]
              : √5 * ↑p = √5 * ((↑p : ℚ) : ℝ)
            )]
            refine Irrational.mul_rat ?_ ?_
            apply Nat.Prime.irrational_sqrt
            exact prime_five
            exact cast_ne_zero.mpr hp
          exact (hNI hI).elim
      rw [hx] at hmnp
      have := this m n p hp hvm hmnp
/-
Plugging that in $100m+10n+p$, the result hold.
-/
      rw [this.1, this.2.1, this.2.2]

/-
Another of the two roots is $\frac{-\sqrt{5} - 1}{8}$, by analyzing rationality and sign, we show this is impossible
-/
    . rw [hsv] at hx
      rw [(by
          rw [(by
            rw [(by rfl: (16 * 5) = (((16 : ℕ) : ℝ) * ((5 : ℕ) : ℝ)))]
            rw [(by rfl: (80) = ((80 : ℕ) : ℝ))]
            rw [← cast_mul]
            : (80:ℝ) = 16 * 5)]
          rw [Real.sqrt_mul]
          simp only [mul_eq_mul_right_iff, ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_false]
          refine Real.sqrt_eq_cases.mpr ?_
          left
          constructor
          . linarith
          . linarith
          . linarith
        : (√80 : ℝ) = (4 * √5))] at hx
      rw [(by
        linarith
        : (-4 - 4 * √5) / (2 * 16) = (-√5 - 1) / 8)] at hx
/-
Plugging the value of x we get $\frac{-\sqrt{5} - 1}{8} = \frac{\sqrt{m}-n}{p}$
Then we have $ -\sqrt{5}p - 8\sqrt{m} = p - 8n$
-/
      have (m n p : ℕ) (hp : p ≠ 0) (hEq : (-√5 - 1) / 8 = (√(m : ℝ) - n) / p) : False := by
        have e: √5  * p + 8 * √m = n * 8 - p := by
          apply_fun (·*(8 :ℝ) * p) at hEq
          have : (√↑m - ↑n) / ↑p * 8 * ↑p = (8 * (√↑m - ↑n)) / ↑p * ↑p := by group
          rw [this] at hEq
          have : (8 * (√↑m - ↑n)) / ↑p * ↑p = 8 * (√↑m - ↑n) := by
            refine IsUnit.div_mul_cancel ?_ (8 * (√↑m - ↑n))
            rw [isUnit_iff_ne_zero]
            exact cast_ne_zero.mpr hp
          rw [this] at hEq
          linarith
        by_cases h : √5  * p + 8 * √m = 0
/-
When $-\sqrt{5}p + 8\sqrt{m} = 0$, a sign problem occurs
-/
        . have : p = -8 * √m / √5 := by
            apply_fun (· - 8 * √m) at h
            rw [add_sub_assoc, sub_self, add_zero, zero_sub] at h
            apply_fun (· / √5) at h
            simp only [ne_eq, ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
              mul_div_cancel_left₀] at h
            rw [neg_mul]
            exact h
          clear e
          have e: p = -8 * √(m / 5) := by
            rw [Real.sqrt_div, ← mul_div_assoc]
            exact this
            exact cast_nonneg' m
          have : (p : ℝ) ≤ 0 := by
            rw [e, mul_comm]
            apply mul_nonpos_of_nonneg_of_nonpos
            exact Real.sqrt_nonneg (↑m / 5)
            linarith
          contrapose this
          push_neg
          exact (lt_of_le_of_ne (cast_nonneg' p) (Ne.symm (cast_ne_zero.mpr hp)))
/-
When $-\sqrt{5}p + 8\sqrt{m} ≠ 0$, a rationality problem occurs
-/
        . have e1: (5 : ℝ) * ((p: ℝ) * p) - 64 * (m : ℝ)
            = (√5 * (p : ℝ) - 8 * √(m : ℝ)) * (√5 * (p : ℝ) + 8 * √(m : ℝ)) := by
            group
            rw [(by
              rw [zpow_two]
              refine Real.mul_self_sqrt ?_
              simp only [ofNat_nonneg]
              : √5 ^ (2 : ℤ) = 5)]
            rw [zpow_two √↑m]
            congr
            refine Eq.symm (Real.mul_self_sqrt ?_)
            simp only [cast_nonneg]
          apply_fun (· * (√5 * ↑p + 8 * √↑m)⁻¹) at e1
          conv at e1 =>
            right
            rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
          have hNI : ¬Irrational (√5 * ↑p) := by
            rw [(by
              group
              : √5 * ↑p = ((√5 * ↑p + 8 * √↑m) + (√5 * ↑p - 8 * √↑m)) / 2)]
            rw [←e1, e, ←division_def]
            unfold Irrational
            push_neg
            use ((↑n * 8 - ↑p + (5 * (↑p * ↑p) - 64 * ↑m) / (↑n * 8 - ↑p)) / 2  : ℚ)
            simp only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
              Rat.cast_natCast]
          have hI : Irrational (√5 * ↑p) := by
            rw [(by
              simp only [Rat.cast_natCast]
              : √5 * ↑p = √5 * ((↑p : ℚ) : ℝ)
            )]
            refine Irrational.mul_rat ?_ ?_
            apply Nat.Prime.irrational_sqrt
            exact prime_five
            exact cast_ne_zero.mpr hp
          exact (hNI hI).elim
      rw [hx] at hmnp
      exact (this m n p hp hmnp).elim
    . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]