import Mathlib

/- `n / m` is composite positive number. -/
def IsQuotPosComp (n m : ℤ) : Prop :=
  m ≠ 0 ∧ m ∣ n ∧ 2 ≤ n / m ∧ ¬ Prime (n / m)

/- Find all values of the positive integer  $k$  that has the property:
There are no positive integers  $a,b$  such that the expression  $A(k,a,b)=\frac{a+b}{a^2+k^2b^2-k^2ab}$  is a composite positive number.-/
theorem number_theory_8949 {k : ℤ} (hkpos : 0 < k) :
    (¬ ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ IsQuotPosComp (a + b) (a ^ 2 + k ^ 2 * b ^ 2 - k ^ 2 * a * b)) ↔
    k = 1 := by
  constructor
  . intro h
    push_neg at h
    suffices k < 2 by interval_cases k; trivial
    by_contra hk
    push_neg at hk
    -- Note that  $A\left( k,k^{2} -1,1\right) =k^{2}$ .
    -- Therefore,  for any  $k \geq 2$ ,  $k$  does not have the property.
    specialize h (k ^ 2 - 1) 1 (by nlinarith) (by norm_num)
    contrapose! h
    unfold IsQuotPosComp
    ring_nf
    norm_num
    nlinarith
  intro hk
  rw [hk]
  clear k hkpos hk
  push_neg
  intro a b ha hb
  ring_nf
  -- WLOG,  $a< b$ .
  wlog hab : a ≤ b
  . push_neg at hab
    rw [add_comm a b, mul_comm a b, add_assoc, add_comm (a ^ 2), ← add_assoc]
    apply this
    . exact hb
    . exact ha
    omega
  rw [le_iff_lt_or_eq, or_comm] at hab
  rcases hab with hab | hab
  -- We will show that  $A( 1,a,b) \leq 2$ . $A( 1,a,a) =\frac{2a}{a^{2}} =\frac{2}{a} \leq 2$ .
  . rw [← hab]
    ring_nf
    unfold IsQuotPosComp
    push_neg
    intro _ _ h
    suffices a * 2 / a ^ 2 ≤ 2 by
      have : a * 2 / a ^ 2 = 2 := le_antisymm this h
      rw [this, Int.prime_iff_natAbs_prime]
      norm_num
    have : a ≠ 0 := by positivity
    rw [pow_two]
    field_simp
    apply Int.ediv_le_of_le_mul
    . positivity
    omega
  -- $A( 1,a,b) =\frac{a+b}{a^{2} +b( b-a)} \leq \frac{a+b}{a^{2} +b} \leq \frac{a+b}{a+b} =1$ .
  unfold IsQuotPosComp
  push_neg
  intro _ h _
  suffices (a + b) / (-(a * b) + a ^ 2 + b ^ 2) ≤ 1 by linarith
  qify
  have intCast_of_dvd {a b : ℤ} (hba : b ∣ a) : ((a / b : ℤ) : ℚ) = (a : ℚ) / (b : ℚ) := by
    rcases hba with ⟨k, rfl⟩
    simp
  rw [intCast_of_dvd h]
  have : a + b ≤ a ^ 2 + b ^ 2 - a * b := by nlinarith
  have div_le_of_le {a b c : ℚ} (hb : 0 < b) (hc : 0 < c) (hba : b ≤ a) : c / a ≤ c / b := by
    rw [div_le_div_left]
    . exact hba
    . exact hc
    . linarith
    exact hb
  have add_ab_pos : 0 < a + b := by positivity
  qify at this add_ab_pos
  have := div_le_of_le add_ab_pos add_ab_pos this
  convert this using 1
  . conv_lhs => rhs; rw [add_assoc, add_comm, ← sub_eq_add_neg]
    norm_cast
  . rw [div_self (by positivity)]
