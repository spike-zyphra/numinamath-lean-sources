import Mathlib

/- 3-ча 1. Solve the equation $x^{y}=y^{x}(x \neq y)$ in natural numbers. Find all solutions. -/

--We first prove that under the given hypotheses, x is nonzero.
lemma x_nezero (x y : ℕ) (hxy : x ≠ y) : x^y = y^x → x ≠ 0 := by
  intro h
  by_contra! x0
  subst x0
  rw [pow_zero, zero_pow hxy.symm] at h
  linarith


--Similarly we prove that y is nonzero as well.
lemma y_nezero (x y : ℕ) (hxy : x ≠ y) : y^x = x^y → y ≠ 0 := by
  intro h
  by_contra! y0
  subst y0
  rw [pow_zero, zero_pow hxy] at h
  linarith

--Assuming that x < y, we now prove that, for all primes p, the p-adic valuation of x is smaller than or equal to that of y.
lemma padic_val (x y p : ℕ) (hxy : x < y) (hp : Nat.Prime p) : x^y = y^x → padicValNat p x ≤ padicValNat p y := by
  intro h
  have padic : padicValNat p (x ^ y) = padicValNat p (y ^ x) := by
    rw [h]
  have hpprime : Fact (Nat.Prime p) := Fact.mk hp
  rw [padicValNat.pow, padicValNat.pow] at padic
  · by_contra! le
    have hlt : x * padicValNat p y < y * padicValNat p x := by
      gcongr
    linarith
  · exact y_nezero x y (by linarith) h.symm
  · exact x_nezero x y (by linarith) h

--We will need the following inequality, that we prove by induction.
lemma ineq (d : ℕ) : 3 + d < 2 ^ d * 4 := by
  induction' d with n hn
  · omega
  · ring_nf
    linarith

--We will need the following inequality as well, that we also prove by induction.
lemma ineq' (c' d : ℕ) (dpos : d > 0) : (2 + d) ^ (c' + 1) > 1 + (c' + 1) := by
  induction' c' with n hn
  · ring_nf
    linarith
  · rw [pow_add, pow_one, ← add_assoc]
    have : 1 + (n + 1) + 1 < (1 + (n + 1)) * (2 + d) := by
      ring_nf
      rw [(by ring_nf : 4 + n * 2 + n * d + d * 2 = (3 + n) + (1 + n + n * d + d * 2))]
      simp
    apply lt_trans this
    gcongr

--Finally, we prove the theorem assuming that x < y.
lemma aux (x y : ℕ) (hxy : x < y) : x^y = y^x → (x = 2 ∧ y = 4) := by
  intro h
--First we prove that x divides y. To do so, we consider the prime factorizations of x and y and we use the lemma "padic_val" proved above.
  have xdvdy : x ∣ y := by
    rw [← Nat.factorization_prime_le_iff_dvd]
    · intro p hpprime
      rw [Nat.factorization, Nat.factorization]
      simp only [Finsupp.coe_mk, hpprime, ↓reduceIte]
      apply padic_val x y p hxy hpprime h
    · exact x_nezero x y (by linarith) h
    · exact y_nezero x y (by linarith) h.symm
  obtain ⟨k,hk⟩:= xdvdy
--Now we write y = x * k, with k > 1.
  have kgt1 : k > 1 := by
    by_contra! k1
    interval_cases k
    all_goals linarith
  rw [gt_iff_lt, lt_iff_exists_add] at kgt1
  obtain ⟨c,cpos,hc⟩ := kgt1
--We rewrite k as 1 + c, which is possible since k > 1, with c positive.
  have hc' : c = k - 1 := by omega
  have h' := h
--Simplifying the equality we obtain x ^ c = 1 + c.
  rw [hk, pow_mul, mul_pow, hc, pow_add, pow_one] at h'
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq, and_not_self, or_false] at h'
  rw [← pow_mul, mul_comm, pow_mul] at h'
  apply Nat.pow_left_injective (x_nezero x y (by linarith) h) at h'
--We need to show that x = 2. We consider the cases x = 1, x = 2, x > 2 separately.
  by_cases xle1 : x ≤ 1
--If x ≤ 1, which is equivalent to x = 1, we obtain a contradiction.
  · have : x = 1 := by
      have := x_nezero x y (by linarith) h
      omega
    subst x
    ring_nf at h
    linarith
--If x = 2, we obtain a solution, with c = 1 and y = 4.
  · by_cases x2 : x = 2
    · subst x
      by_cases c0 : c = 0
--If c = 0 we have a contradiction
      · linarith
      · by_cases c1 : c = 1
--If c = 1 we find the solution (x,y)=(2,4).
        · subst c1
          norm_num at hc
          subst k
          norm_num at hk
          subst y
          exact ⟨rfl,rfl⟩
--If c ≥ 2 we find a contradiction, using the first inequality proven above.
        · have cge2 : 2 ≤ c := by omega
          rw [le_iff_exists_add] at cge2
          obtain ⟨d,hd⟩ := cge2
          subst hd
          ring_nf at h'
          have := ineq d
          linarith
--If x > 2, we find again a contradiction, using the second inequality proven above.
    · have xgt2 : 2 < x := by omega
      rw [lt_iff_exists_add] at xgt2
      obtain ⟨d,dpos,hd⟩ := xgt2
      rw [hd] at h'
      have : c ≥ 1 := by omega
      rw [ge_iff_le, le_iff_exists_add] at this
      obtain ⟨c',hcc'⟩ := this
      rw [add_comm] at hcc'
      have := ineq' c' d dpos
      rw [← hcc'] at this
      linarith

--We are now ready to prove the theorem
theorem number_theory_283863 (x y : ℕ) (hxy : x ≠ y) : x^y = y^x ↔ (x = 2 ∧ y = 4) ∨ (x = 4 ∧ y = 2) := by
  constructor
--We first assume that x < y, and apply the lemma "aux".
  · by_cases hxlty : x < y
    · intro h
      apply aux x y hxlty at h
      tauto
--If instead y < x, we can apply the lemma "aux" again, with the roles of x and y switched.
    · have hyx : y < x := by
        rw [lt_iff_le_and_ne]
        rw [not_lt] at hxlty
        exact ⟨hxlty, hxy.symm⟩
      intro h
      symm at h
      apply aux y x hyx at h
      tauto
--To conclude, we prove that (2,4) and (4,2) are indeed solutions.
  · intro h
    rcases h with h | h
    all_goals obtain ⟨hx, hy⟩ := h; subst hx; subst hy; linarith