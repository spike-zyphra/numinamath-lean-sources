import Mathlib

open Polynomial

/- Find the smallest positive integer n with the property that the polynomial x^4−nx+63x can be written
as a product of two nonconstant polynomials with integer coefficients. -/
theorem algebra_94694 :
    IsLeast {n : ℤ | n > 0 ∧ ∃ q r : Polynomial ℤ,
      1 ≤ q.natDegree ∧ 1 ≤ r.natDegree ∧
      X ^ 4 - C n * X + 63 = q * r} 8 := by
  -- we need to show that p = X ^ 4 - 8 * X + 63 can be written as a product of
  -- two nonconstant polynomials and that if p = q * r with nonconstant q and r
  -- then 8 ≤ n
  simp only [IsLeast, gt_iff_lt, eq_intCast, Set.mem_setOf_eq, Nat.ofNat_pos,
    Int.cast_ofNat, true_and, lowerBounds, and_imp, forall_exists_index]
  constructor
  -- if n = 8 then take q = X ^ 2 - 4 * X + 7 and r = X ^ 2 + 4 * X + 9
  -- and show that p = q * r
  · use X ^ 2 - 4 * X + 7, X ^ 2 + 4 * X + 9
    rw [show (X ^ 2 - 4 * X + 7 : Polynomial ℤ).natDegree = 2 by compute_degree <;> norm_num]
    rw [show (X ^ 2 + 4 * X + 9 : Polynomial ℤ).natDegree = 2 by compute_degree <;> norm_num]
    norm_num
    ring
  -- now we have p = q * r with nonconstant p and q
  -- we need to show that 8 ≤ n
  have hc0 {k} (c : ℤ) (hk : 1 ≤ k) : (c : Polynomial ℤ).coeff k = 0 := by compute_degree; omega
  intro n hn q r hq hr heq
  set p : Polynomial ℤ := X ^ 4 - _ + _
  have hp_deg : p.natDegree = 4 := by simp [p]; compute_degree!
  have hp0 : p.coeff 0 = 63 := by simp [p]
  have hp1 : p.coeff 1 = -n := by simp [p]
  have hp2 : p.coeff 2 = 0 := by simp [p, hc0]
  have hp3 : p.coeff 3 = 0 := by simp [p, hc0]
  have hp4 : p.coeff 4 = 1 := by simp [p, hc0]
  -- without loss of generality assume that the degree of q ≤ the degree of r
  wlog hqr_deg : q.natDegree ≤ r.natDegree generalizing q r
  · apply this r q hr hq (by rwa [mul_comm]) (by omega)
  -- without loss of generality assume that the leading coefficient of q is positive
  wlog hq1 : 0 < q.leadingCoeff generalizing q r
  · apply this (-q) (-r) <;> simp [natDegree_neg, *]
    suffices q.leadingCoeff ≠ 0 by simp; omega
    rw [leadingCoeff_ne_zero]
    exact ne_zero_of_natDegree_gt hq
  -- it is easy to show that q and r are monic polynomials because p is monic
  -- and the leading coefficient of q is positive:
  -- 1 = p.leadingCoeff = q.leadingCoeff * r.leadingCoeff
  -- we get q.leadingCoeff = r.leadingCoeff = 1
  have ⟨hqm, hrm⟩ : q.Monic ∧ r.Monic := by
    simp_rw [Monic]
    apply_fun leadingCoeff at heq
    rw [leadingCoeff_mul] at heq
    have : p.leadingCoeff = 1 := by rw [leadingCoeff, hp_deg, hp4]
    rw [this, eq_comm, Int.mul_eq_one_iff_eq_one_or_neg_one] at heq
    omega
  -- we have two cases: the degree of q is 1 and the degree of r is 3
  -- or the degree of q is 2 and the degree of r is 2
  replace hqr_deg : q.natDegree = 1 ∧ r.natDegree = 3 ∨ q.natDegree = 2 ∧ r.natDegree = 2 := by
    have := Monic.natDegree_mul hqm hrm
    rw [← heq, hp_deg] at this
    omega
  -- prove some auxiliary results about polynomials of degrees 1, 2, 3, 4
  have h1 {p : Polynomial ℤ} (hm : p.Monic) (hdeg : p.natDegree = 1) : ∃ a : ℤ, p = X + C a := by
    use p.coeff 0
    exact Monic.eq_X_add_C hm hdeg
  have h2 {p : Polynomial ℤ} (hm : p.Monic) (hdeg : p.natDegree = 2) : ∃ a b : ℤ, p = X ^ 2 + C a * X + C b := by
    use p.coeff 1, p.coeff 0
    rw [Monic.as_sum hm, hdeg]
    apply Polynomial.funext
    intro x
    simp [Finset.sum, hc0]
    ring
  have h3 {p : Polynomial ℤ} (hm : p.Monic) (hdeg : p.natDegree = 3) : ∃ a b c : ℤ, p = X ^ 3 + C a * X ^ 2 + C b * X + C c := by
    use p.coeff 2, p.coeff 1, p.coeff 0
    rw [Monic.as_sum hm, hdeg]
    apply Polynomial.funext
    intro x
    simp [Finset.sum, hc0]
    ring
  have heqs {a b c d : ℤ} (h : q * r = X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) :
      a = 0 ∧ b = 0 ∧ c = -n ∧ d = 63 := by
    simp_rw [← heq, p, Polynomial.ext_iff] at h
    constructorm* _ ∧ _ <;> [specialize h 3; specialize h 2; specialize h 1; specialize h 0]
    all_goals { simp [hc0] at h ⊢; omega }
  cases' hqr_deg with hqr hqr
  -- let q = X + a and r = X ^ 3 + b * X ^ 2 + c * X + d
  · replace ⟨a, hq⟩ := h1 hqm hqr.1
    replace ⟨b, c, d, hr⟩ := h3 hrm hqr.2
    replace hqr : q * r = X ^ 4 + C (a + b) * X ^ 3 + C (a * b + c) * X ^ 2 + C (a * c + d) * X + C (a * d) := by
      simp [hq, hr]; ring
    -- from p = q * r we get the following equalities:
    -- a * d = 63
    -- a * c + d = -n
    -- a * b + c = 0
    -- a + b = 0
    have ⟨eq3, eq2, eq1, eq0⟩ := heqs hqr
    clear * - hn eq0 eq1 eq2 eq3
    -- derive that d = -n - a ^ 3
    have hd : d = -n - a ^ 3 :=
      calc
        d = -n - a * c := by omega
        _ = -n - a * (-a * b) := by congr; linarith
        _ = -n - a * (-a * -a) := by congr; omega
        _ = -n - a ^ 3 := by ring
    -- it follows that a < 0 because 0 < 63 = a * d = -a * (n + a ^ 3) and n > 0
    have ha_neg : a < 0 := by
      contrapose! eq0
      rw [hd, show a * (-n - a ^ 3) = -(a * (n + a ^ 3)) by ring]
      have : 0 ≤ a * (n + a ^ 3) := by positivity
      omega
    -- a < 0 implies that d < 0 (because a * d = 63)
    have hd_neg : d < 0 := by
      contrapose! eq0
      have : a * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) eq0
      omega
    -- d < 0 implies that -n < a ^ 3
    have ha : -n < a ^ 3 := by omega
    -- consider two cases: a = -1 and a ≤ -2
    cases' show a = -1 ∨ a ≤ -2 by omega with h h
    · replace hd : d = -63 := by rw [h] at eq0; omega
      -- if a = -1 then d = -63 and we get n = -d - a ^ 3 = 63 + 1 = 64 ≥ 8
      calc
        8 ≤ -(-1 * 1 + -63) := by norm_num
        _ = -(-n) := by subst a d; linarith
        _ = n := by rw [neg_neg]
    -- if a ≤ -2 then 8 ≤ (-a) ^ 3 < n
    · calc
        8 ≤ 2 ^ 3 := by norm_num
        _ ≤ (-a) ^ 3 := pow_le_pow_left₀ zero_le_two (by omega) 3
        _ = -a ^ 3 := by ring
        _ ≤ n := by omega
  -- let q = X ^ 2 + a * X + b and r = X ^ 2 + c * X + d
  · replace ⟨a, b, hq⟩ := h2 hqm hqr.1
    replace ⟨c, d, hr⟩ := h2 hrm hqr.2
    replace hqr : q * r = X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X + C (b * d) := by
      simp [hq, hr]; ring
    -- from p = q * r we get the following equalities:
    -- b * d = 63
    -- a * d + b * c = -n
    -- b + d + a * c = 0
    -- a + c = 0
    have ⟨eq3, eq2, eq1, eq0⟩ := heqs hqr
    clear * - hn eq0 eq1 eq2 eq3
    -- it is easy to derive that b + d = a ^ 2
    have hbd : b + d = a ^ 2 := calc
      b + d = -(a * c) := by omega
      _ = -(a * (-a)) := by congr; omega
      _ = a ^ 2 := by ring
    -- show that 0 < b and 0 < d
    have ⟨hb, hd⟩ : 0 < b ∧ 0 < d := by
      -- 0 < 63 = b * d
      have : 0 < b * d := by omega
      -- we have 0 < b and 0 < d or b < 0 and d < 0
      rw [mul_pos_iff] at this
      cases' this with h h <;> [assumption; skip]
      -- if b < 0 and d < 0 then b + d < 0 ≤ a ^ 2, a contradiction
      contrapose! hbd
      apply ne_of_lt
      calc
        b + d < 0 := by omega
        _ ≤ a ^ 2 := by positivity
    lift b to ℕ using (le_of_lt hb)
    lift d to ℕ using (le_of_lt hd)
    replace hd : d = 63 / b := by symm; apply Nat.div_eq_of_eq_mul_right <;> zify <;> omega
    -- all possible values of b are divisors of 63
    replace hb : b ∈ ({1, 3, 7, 9, 21, 63} : Finset ℕ) := by
      rw [show {1, 3, 7, 9, 21, 63} = (63).divisors from rfl]
      simp
      use d
      zify
      rw [eq0]
    simp at hb
    -- consider all possible values of b and find that b + d = a ^ 2
    -- iff b = 1, d = 63 or b = 7, d = 9 or b = 63, d = 1, or b = 9, d = 7
    -- in all these cases 8 ≤ n
    rcases hb with h | h | h | h | h | h <;> (subst b; norm_num at hd; subst d) <;> try omega
    · suffices a = 4 ∨ a = -4 by omega
      rw [← sq_eq_sq_iff_eq_or_eq_neg, ← hbd]
      norm_num
    · suffices a = 4 ∨ a = -4 by omega
      rw [← sq_eq_sq_iff_eq_or_eq_neg, ← hbd]
      norm_num