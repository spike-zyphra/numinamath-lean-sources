import Mathlib
open Complex

-- Find the smallest positive integer $n$ such that there exists a complex number $z$, with positive real and imaginary part, satisfying $z^{n}=(\bar{z})^{n}$.
theorem algebra_609449 : (∀ n > 0, (∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z ^ n = ((starRingEnd ℂ) z) ^ n) → 3 ≤ n) ∧
  (∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z ^ 3 = ((starRingEnd ℂ) z) ^ 3) := by
  constructor
  intro n hn ⟨z,hz1,hz2,hz3⟩
  -- Since $|z|=|\bar{z}|$ we may divide by $|z|$ and assume that $|z|=1$.
  have heq : abs z = abs ((starRingEnd ℂ) z) := by
    have : (abs z) ^ n = (abs ((starRingEnd ℂ) z)) ^ n := by
      rw [← abs_pow,← abs_pow,hz3]
    apply (pow_eq_pow_iff_of_ne_zero (Nat.not_eq_zero_of_lt hn)).mp at this
    rcases this with h | ⟨h1,h2⟩
    · exact h
    replace h1 : Complex.abs z + Complex.abs ((starRingEnd ℂ) z) = 0 := by rw [h1] ;simp
    apply (add_eq_zero_iff_of_nonneg (AbsoluteValue.nonneg Complex.abs z) (AbsoluteValue.nonneg Complex.abs ((starRingEnd ℂ) z))).mp at h1
    simp at h1 ;simp [h1] at hz1
  let z' := z / abs z
  have hz' : abs z' = 1 := by
    simp [z',abs_div] ;ring_nf ;apply (mul_inv_eq_one₀ ?_).mpr ;rfl
    by_contra hz' ;simp at hz' ;simp [hz'] at hz1
  -- Then $\bar{z}=\frac{1}{z}$, so we are looking for the smallest positive integer $n$ such that there is a $2 n^{\text {th }}$ root of unity in the first quadrant.
  have hz'eq : z' = 1 / (starRingEnd ℂ z') := by
    have : z' * (starRingEnd ℂ z') = 1 := by
      rw [mul_conj,Complex.normSq_eq_abs,hz'] ;simp
    rw [← this,mul_div_cancel_right₀]
    by_contra hz' ;simp [z'] at hz' ;simp [hz'] at hz1
  have hz3' : z' ^ n = (starRingEnd ℂ z') ^ n := by simp [z',div_pow,hz3]
  have h : (z' ^ n) * (starRingEnd ℂ z') ^ n = 1 := by
    nth_rewrite 1 [hz'eq,← mul_pow,div_mul_cancel₀,one_pow] ;rfl
    by_contra hz' ;simp [z'] at hz' ;simp [hz'] at hz1
  rw [← hz3',← pow_add] at h
  have hz2' : 0 < z'.im := by
    simp [z'] ;apply div_pos ;exact hz2 ;refine AbsoluteValue.pos Complex.abs ?_
    by_contra hz ;simp [hz] at hz1
  have hz1' : 0 < z'.re := by
    simp [z'] ;apply div_pos ;exact hz1 ;refine AbsoluteValue.pos Complex.abs ?_
    by_contra hz ;simp [hz] at hz1
  -- Clearly there is a sixth root of unity in the first quadrant but no fourth or second roots of unity, so $n=3$ is the smallest.
  by_cases hn1 : n = 1
  · simp [hn1] at h
    rcases h with h | h
    simp [h] at hz2' ;simp [h] at hz2'
  by_cases hn2 : n = 2
  · simp [hn2] at h
    have : 4 = 2*2 := rfl
    rw [this,pow_mul] at h
    simp at h
    rcases h with h | h
    rcases h with h | h
    simp [h] at hz2' ;simp [h] at hz2'
    rw [← Complex.I_sq] at h
    have : (z' - I) * (z' + I) = 0 := by
      rw [sub_mul,mul_add,mul_add,← pow_two,h] ;ring
    simp at this
    rcases this with h | h
    have : z' = 0 + I := by exact Eq.symm (add_eq_of_eq_sub (id (Eq.symm h)))
    simp at this ;simp [this] at hz1'
    have : z' = 0 - I := by exact Eq.symm (sub_eq_of_eq_add (id (Eq.symm h)))
    simp at this ;simp [this] at hz1'
  refine Nat.succ_le_of_lt (Nat.two_lt_of_ne (Nat.not_eq_zero_of_lt hn) hn1 hn2)
  use (0.5+0.5*√3*I) ;norm_num
  have : (starRingEnd ℂ) 2 = 2 := by exact conj_eq_iff_re.mpr rfl
  rw [this] ;simp ;ring_nf
  have : I ^ 3 = -I := by rw [pow_three,← pow_two] ;simp
  rw [this] ;ring_nf
  have : ↑√3 ^ 3 = √3 * (3:ℂ) := by rw [pow_three,← ofReal_mul,← pow_two] ;simp
  rw [this] ;ring_nf
  