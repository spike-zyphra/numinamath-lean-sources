import Mathlib

open Polynomial Complex ComplexConjugate

/- 5. If the expansion of $\left(1+x+x^{2}\right)^{1000}$ is $a_{0}+a_{1} x+a_{2} x^{2}+\cdots+a_{2000} x^{2000}$, then the value of $a_{0}+a_{3}+$ $a_{6}+a_{9}+\cdots+a_{1998}$ is
A. $3^{333}$
B. $3^{666}$
C. $3^{999}$
D. $3^{2001}$ -/

-- define omega = 3rd root of unity
noncomputable
def ω : ℂ := - 1 / 2 + √3 / 2 * I

-- √3^2 = 3 in complex numbers, used severa time
lemma l_sqrt_three_complex_sq : √3 ^ 2 = (3 : ℂ) := by
    norm_cast
    simp

-- omega ^ 2's value
lemma l_omega_sq : ω ^ 2 = - 1 / 2 - √3 / 2 * I := by
  simp [ω]
  ring_nf
  rw [l_sqrt_three_complex_sq]
  simp
  ring

-- omega^2 is conjugate of omega
lemma l_omega_conj : conj ω = ω ^ 2 := by
  rw [l_omega_sq]
  simp [ω]
  rw [show (2 : ℂ) = ↑(2 : ℝ) by norm_cast, Complex.conj_ofReal]
  norm_cast

-- omega^3 = 1
lemma l_omega_pow_three : ω ^ 3 = 1 := by
  rw [pow_succ, l_omega_sq]
  simp [ω]
  ring_nf
  rw [l_sqrt_three_complex_sq]
  simp
  norm_num

-- omega ^ n can be converted to power modulo 3
lemma l_omega_pow (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  nth_rw 1 [← Nat.mod_add_div n 3]
  ring_nf
  rw [mul_comm (n/3), pow_mul, l_omega_pow_three]
  simp

-- omega + omega^2 = -1
lemma l_omega_add_omega_sq_add_one_eq_zero : 1 + ω + ω^2 = 0 := by
  rw [l_omega_sq]
  simp [ω]
  ring

-- x * (1 + omega^n + omega^(2n)) is 3x if n is divisble by 3
lemma l_omega_add_omega_sq_add_one_eq_zero' (x : ℂ) (n : ℕ) (h : n % 3 = 0) : x + x * ω^n + x * (ω^2)^n = 3 * x := by
  rw [← Nat.div_add_mod n 3, h]
  ring_nf
  rw [mul_comm (n/3), pow_mul, l_omega_pow_three]
  rw [show 6 = 2 * 3 by norm_num, mul_comm 2, ← mul_assoc, mul_comm (n/3), mul_assoc, pow_mul, l_omega_pow_three]
  simp
  ring

-- x * (1 + omega^n + omega^(2n)) is 0 if n is divisble by 3 is not divisible by 3, in this case the mod of n by 3 is 1 or 2, in both case sum is 0
lemma l_omega_add_omega_sq_add_one_eq_zero'' (x : ℂ) (n : ℕ) (h : n % 3 ≠ 0) : x + x * ω^n + x * (ω^2)^n = 0 := by
  rw [← Nat.div_add_mod n 3]
  have : 0 < n % 3 := by apply Nat.zero_lt_of_ne_zero h
  have : n % 3 < 3 := by apply Nat.mod_lt _ (by norm_num)
  interval_cases n % 3
  . rw [← pow_mul]
    ring_nf
    rw [l_omega_pow]
    simp
    rw [l_omega_pow (n/3 * 6), Nat.mul_mod]
    norm_num
    rw [show  x + x * ω + x * ω ^ 2 = x * (1 + ω + ω^2) by ring, l_omega_add_omega_sq_add_one_eq_zero]
    simp
  . rw [← pow_mul]
    ring_nf
    rw [l_omega_pow (n/3 * 3)]
    simp
    rw [l_omega_pow (n/3 * 6), Nat.mul_mod]
    norm_num
    rw [l_omega_pow 4]
    norm_num
    rw [show  x + x * ω^2 + x * ω = x * (1 + ω + ω^2) by ring, l_omega_add_omega_sq_add_one_eq_zero]
    simp

theorem algebra_225644 (A : ℝ[X]) (h : (1 + X + X^2)^1000 = A) (hdeg : A.natDegree = 2000) :
    ∑ i in (Finset.Ico 0 2001).filter (fun i => i % 3 = 0), A.coeff i = 3^999 := by
  -- first we convert the polynomials to ℂ and also change 1000 to a variable n (as leant can't handle large number in power)
  let B := map (algebraMap ℝ ℂ) A
  replace h := congrArg (fun x ↦ map (algebraMap ℝ ℂ) x) h
  convert_to (1 + X + X^2)^1000 = B at h
  . simp
  rw [show 2000 = 2 * 1000 by norm_num] at hdeg
  rw [show 2001 = 2 * 1000 + 1 by norm_num]
  generalize hn : 1000 = n  at h hdeg
  -- evaluate B at 1, ω, ω^2 and add them
  have hω : B.eval 1 + B.eval ω + B.eval (ω^2) = 3^n := by
    rw [← h]
    simp
    ring_nf
    rw [l_omega_pow 4]
    norm_num
    ring_nf
    rw [l_omega_add_omega_sq_add_one_eq_zero]
    simp
    rw [← hn]
    norm_num
  replace hdeg : B.natDegree = 2 * n := by simpa [B]
  -- write evaluation as sum of x^i, combine them
  simp [Polynomial.eval_eq_sum_range] at hω
  rw [hdeg, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.range_eq_Ico] at hω
  -- divdie the sum to indices divisible by 3 and those not divisible by 3
  rw [← Finset.sum_filter_add_sum_filter_not (p := fun i ↦ i % 3 = 0)] at hω
  -- the ones divisible ty 3 turn to be just 3 * coefficient, and not divibielby 3 zero out
  convert_to (∑ x ∈ Finset.filter (fun x => x % 3 = 0) (Finset.Ico 0 (2 * n + 1)), 3 * B.coeff x) + 0 = 3 ^ n at hω
  . congr 1
    . apply Finset.sum_congr rfl
      rintro i hi
      simp at hi
      apply l_omega_add_omega_sq_add_one_eq_zero'
      exact hi.right
    . apply Finset.sum_eq_zero
      rintro i hi
      simp at hi
      apply l_omega_add_omega_sq_add_one_eq_zero''
      exact hi.right
  -- now casting back to A, we get our goal
  rw [← Finset.mul_sum, show n = n - 1 + 1 by omega, pow_succ, mul_comm _ 3] at hω
  simp at hω
  rw [show 2 * (n - 1 + 1) + 1 = 2 * n + 1 by omega] at hω
  simp [B] at hω
  norm_cast at hω
  push_cast at hω
  rw [Finset.range_eq_Ico] at hω
  rw [hω, ← hn]