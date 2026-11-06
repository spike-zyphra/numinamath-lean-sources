import Mathlib

set_option maxHeartbeats 400000

/-Find all triples $(x, y, z)$ of positive integers such that $x \leq y \leq z$ and  $$ x^{3}\left(y^{3}+z^{3}\right)=2012(x y z+2) \text {. } $$-/
theorem N2 {x y z : ℤ} (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z) :
  x^3 * (y^3 + z^3) = 2012 * (x * y * z + 2) ↔ x = 2 ∧ y = 251 ∧ z = 252 := by
  constructor <;> intro h
  · have c1 : x^3 ∣ 2012 * (x * y * z + 2) := Dvd.intro _ h
    -- An auxiliary lemma : 503 is prime.
    have prime503 : Prime (503 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by native_decide)
    -- First note that $x$ divides $2012 \cdot 2=2^{3} \cdot 503$.
    have h1 : x ∣ 2012 * 2 := by
      have : x ∣ 2012 * (x * y * z + 2) :=
        (Dvd.intro_left (x^2) rfl).trans (Dvd.intro _ h)
      ring_nf at this ⊢
      convert dvd_sub this (show x ∣ x * y * z * 2012 by simp [mul_assoc])
      ring
    replace h1 : x ∣ 2^3 * 503 := by simp_all
    -- If $503 \mid x$ then the right-hand side of the equation is divisible by $503^{3}$, and it follows that $503^{2} \mid x y z+2$. This is false as $503 \mid x$.
    -- Hence $x=2^{m}$ with $m \in\{0,1,2,3\}$.
    have h2 : (x = 1 ∨ x = 2) ∨ (x = 4 ∨ x = 8) := by
      have h2 : IsCoprime x 503 := by
        rw [isCoprime_comm, Prime.coprime_iff_not_dvd
          (Int.prime_iff_natAbs_prime.mpr (by native_decide))]
        intro h3
        have h3' := (pow_dvd_pow_of_dvd h3 3).trans (Dvd.intro _ h)
        have h4 : (503 : ℤ) ∣ 2 := by
          have h4 : 503^2 ∣ (x * y * z + 2) := by
            rw [show (503 : ℤ)^3 = 503 * 503^2 by simp,
              show (2012 : ℤ) = 503 * 4 by norm_num, mul_assoc] at h3'
            have := Int.dvd_of_mul_dvd_mul_left (by simp) h3'
            refine IsCoprime.dvd_of_dvd_mul_left ?_ this
            exact Int.isCoprime_iff_gcd_eq_one.mpr rfl
          replace h4 : 503 ∣ (x * y * z + 2) := (show (503 : ℤ)∣ 503^2 by norm_num).trans h4
          convert dvd_sub h4
            (show 503 ∣ x* y * z by rw [mul_assoc]; exact dvd_mul_of_dvd_left h3 _)
          ring
        tauto
      have h3 : x ∣ 2 ^ 3 := IsCoprime.dvd_of_dvd_mul_left h2 h1
      have : x ≤ 8 := Int.le_of_dvd (by simp) h3
      interval_cases x <;> tauto
    -- If $m \geq 2$ then $2^{6} \mid 2012(x y z+2)$. However the highest powers of 2 dividing 2012 and $x y z+2=2^{m} y z+2$ are $2^{2}$ and $2^{1}$ respectively.
    -- So $x=1$ or $x=2$
    have h3 : x = 1 ∨ x = 2 := by
      refine (or_iff_left ?_).1 h2
      intro h3
      have h4 : 2^6 ∣ x^3 := by
        rcases h3 with h3 | h3 <;> simp [h3]; norm_num
      replace h4 := h4.trans c1
      have h5 : 4 ∣ (x * y * z + 2) := by
        have h5 : 2 ^ 6 ∣ 2^2 * 503 * (x * y * z + 2) := by simp_all
        have h6 : 2 ^ 4 ∣ 503 * (x * y * z + 2) := by omega
        omega
      have : 4 ∣ x := by rcases h3 with h3 | h3 <;> simp [h3]; norm_num
      have : 4 ∣ 2 := by
        convert dvd_sub h5 (show 4 ∣ x * y * z by
        rw [mul_assoc]; exact Dvd.dvd.mul_right this (y * z)) using 1
        simp
        tauto
      tauto
    -- In both cases the prime $503=3 \cdot 167+2$ divides $y^{3}+z^{3}$. We claim that $503 \mid y+z$.
    have h4 : 503 ∣ y + z := by
      have h5 : 503 ∣ y^3 + z^3 := by
        rcases h3 with h3 | h3 <;> simp [h3] at h
        · exact (show (503 : ℤ) ∣ 2012 by norm_num).trans (Dvd.intro (y * z + 2) h.symm)
        · have : 2012 ∣ 8 * (y ^ 3 + z ^ 3) := Dvd.intro (2 * y * z + 2) h.symm
          have : 503 ∣ 2 * (y ^ 3 + z ^ 3) := by
            rw [show (2012 : ℤ) = 4 * 503 by norm_num,
              show (8 : ℤ) = 4 * 2 by norm_num, mul_assoc] at this
            exact Int.dvd_of_mul_dvd_mul_left (by simp) this
          refine IsCoprime.dvd_of_dvd_mul_left ?_ this
          exact Int.isCoprime_iff_gcd_eq_one.mpr rfl
      by_cases h6 : 503 ∣ y
      · -- This is clear if $503 \mid y$.
        have : 503 ∣ y^3 := by refine Dvd.dvd.pow h6 (by simp)
        have : 503 ∣ z^3 := (Int.dvd_iff_dvd_of_dvd_add h5).mp this
        have : 503 ∣ z := by
          rwa [←Prime.dvd_pow_iff_dvd prime503 (show 3 ≠ 0 by simp)]
        omega
      · -- If $503 \nmid y$, $503 \nmid z$. Then $y^{502} \equiv z^{502}(\bmod 503)$ by FeRmat's little theorem. On the other hand $y^{3} \equiv-z^{3}(\bmod 503)$ implies $y^{3 \cdot 167} \equiv-z^{3 \cdot 167}(\bmod 503)$, i. e. $y^{501} \equiv-z^{501}(\bmod 503)$.
        -- It follows that $y \equiv-z(\bmod 503)$ as claimed.
        have ndvdz : ¬503 ∣ z := by
          contrapose! h6
          have : 503 ∣ z^3 := by refine Dvd.dvd.pow h6 (by simp)
          have : 503 ∣ y^3 := (Int.dvd_iff_dvd_of_dvd_add h5).mpr this
          rwa [←Prime.dvd_pow_iff_dvd prime503 (show 3 ≠ 0 by simp)]
        rw [←Prime.coprime_iff_not_dvd prime503, isCoprime_comm] at h6
        rw [←Prime.coprime_iff_not_dvd prime503, isCoprime_comm] at ndvdz
        have c2 := Int.ModEq.pow_card_sub_one_eq_one (show Nat.Prime 503 by native_decide) h6
        have c3 := Int.ModEq.pow_card_sub_one_eq_one (show Nat.Prime 503 by native_decide) ndvdz
        have c4 := c2.trans c3.symm
        have c5 : y^3 ≡ -z^3 [ZMOD 503] := by
          have := Int.ModEq.sub_right (z^3) (Int.modEq_zero_iff_dvd.2 h5 )
          simp at this
          exact this
        replace c5 : y^501 ≡ -z^501 [ZMOD 503] := by
          have := Int.ModEq.pow 167 c5
          rw [neg_pow, ←pow_mul, ←pow_mul] at this
          ring_nf at this
          exact this
        have c6 : y ≡ -z [ZMOD 503] := by
          ring_nf at c4
          have c6 : y^501 * y ≡ y^501 * (-z) [ZMOD 503] := by
            have c4' : y ^ 501 * y ≡ -z ^ 501 * -z [ZMOD 503] := by
              ring_nf; exact c4
            exact c4'.trans (Int.ModEq.mul c5.symm (by simp))
          have gcd1 : (503 : ℤ).gcd (y^501) = 1 := by
            have : IsCoprime (y^501) 503 := IsCoprime.pow_left h6
            exact Int.gcd_eq_one_iff_coprime.2 (isCoprime_comm.1 this)
          have := Int.ModEq.cancel_left_div_gcd (by simp) c6
          simp [gcd1] at this
          exact this
        have := Int.ModEq.dvd c6.symm
        ring_nf at this
        exact this
    -- y^3 + z^3 = (y + z) * ((y - z)^2 + y * z).
    have c2 : y^3 + z^3 = (y + z) * ((y - z)^2 + y * z) := by nlinarith
    -- we get $x = 2$ because there has contridaction when $x = 1$.
    have h5 : x = 2 := by
      refine (or_iff_right ?_).1 h3
      intro x1
      simp [x1] at h
      obtain ⟨k, hk⟩ := h4
      have h' := h
      simp [c2, hk] at h
      -- when $x = 1$, $k(y-z)^{2}+(k-4) y z=8$
      have c3 : k * (y - z)^2 + (k - 4) * y * z = 8 := by nlinarith
      -- we have $(k-4) y z \leq 8$, which implies $k \leq 4$.
      -- Indeed if $k>4$ then $1 \leq(k-4) y z \leq 8$, so that $y \leq 8$ and $z \leq 8$. This is impossible as $y+z=503 k \geq 503$.
      have kle4 : k ≤ 4 := by
        by_contra! kgt4
        have : (k - 4) * y * z ≤ 8 := by nlinarith
        have aux {a b c: ℤ} (apos : 0 < a) (bpos : 0 < b) (h : a * b ≤ c)
          : a ≤ c ∧ b ≤ c := by
          split_ands <;> by_contra! hfalse
          · have : c < a * b := calc
              _ < a := hfalse
              _ = a * 1 := by omega
              _ ≤ _ := (mul_le_mul_iff_of_pos_left apos).mpr bpos
            linarith
          · have : c < a * b := calc
              _ < b := hfalse
              _ = 1 * b := by omega
              _ ≤ a * b := (Int.mul_le_mul_iff_of_pos_right bpos).mpr apos
            linarith
        have z8 := aux (by apply Int.mul_pos <;> linarith) (by omega) this
        have y8 := (aux (by omega) (by omega) z8.1).2
        linarith
      have kpos : 1 ≤ k := by linarith
      -- Note next that $y^{3}+z^{3}$ is even in the first equation.
      -- Hence $y+z=503 k$ is even too, meaning that $k$ is even. Thus $k=2$ or $k=4$.
      have eveny3z3 : Even (y^3 + z^3) := h' ▸ Int.even_mul.2 <| Or.inl (
        Int.even_iff.mpr rfl)
      have aux {m n : ℤ} (h : Even (m^3 + n^3)) : Even (m + n) := by
        by_contra! odd_add
        simp at odd_add
        rcases Int.even_or_odd m with evenm | oddm
        · have oddn : Odd n := (Int.odd_add'.1 odd_add).2 evenm
          have := (Int.even_add.1 h).1 (Int.even_pow.2 ⟨evenm, by simp⟩)
          exact (Int.not_odd_iff_even.2 <| this) <| Int.odd_pow.2 <| Or.inl oddn
        · have evenn : Even n :=  (Int.odd_add.1 odd_add).1 oddm
          have := (Int.even_add.1 h).2 (Int.even_pow.2 ⟨evenn, by simp⟩)
          exact (Int.not_odd_iff_even.2 <| this) <| Int.odd_pow.2 <| Or.inl oddm
      have evenk : Even k := by
        have := hk ▸ aux eveny3z3
        rw [Int.even_mul] at this
        tauto
      -- Clearly (1) has no integer solutions for $k=4$.
      have k2ork4 : k = 2 ∨ k = 4 := by interval_cases k <;> tauto
      rcases k2ork4 with k2 | k4
      · -- If $k=2$ then (1) takes the form $(y+z)^{2}-5 y z=4$. Since $y+z=503 k=503 \cdot 2$,
        -- this leads to $5 y z=503^{2} \cdot 2^{2}-4$. However $503^{2} \cdot 2^{2}-4$ is not a multiple of 5 .
        simp [k2] at c3 hk
        have c4 : (y + z)^2 - 5 * y * z = 4 := by nlinarith
        have : 5 * (y * z) = 1012032 := by nlinarith
        have : (5 : ℤ) ∣ 1012032 := Dvd.intro (y * z) this
        have : ¬ (5 : ℤ) ∣ 1012032 := by norm_num
        contradiction
      · simp [k4] at c3
        have notIsSq2 {x : ℤ} (h : x^2 = 2) : False := by
          rw [←sq_abs] at h
          have : |x| < 2 := by nlinarith
          rw [abs_lt] at this
          have xgt := this.1
          have xlt := this.2
          interval_cases x <;> tauto
        exact notIsSq2 (show (y - z) ^ 2 = 2 by linarith)
      -- Therefore (1) has no integer solutions. 
    simp [h5] at h
    -- $x = 2$ implies $0 \leq(k-1) y z \leq 1$, so that $k=1$ or $k=2$.
    obtain ⟨k, hk⟩ := h4
    have kpos : 1 ≤ k := by linarith

    simp [c2, hk] at h
    have c3 : k * (y - z)^2 + (k - 1) * y * z = 1 := by nlinarith
    have : (k - 1) * y * z ≤ 1 := by nlinarith
    have : 0 ≤ (k - 1) * y * z := by
      apply_rules [Int.mul_nonneg] <;> linarith
    have k1 : k = 1 := by
      have : k ≤ 2 := by
        by_contra!
        have : 1 < (k - 1) * y * z := by
          calc _ < (k - 1) * 1 * 1 := by linarith
               _ ≤ _ := by
                rw [mul_assoc, mul_assoc]
                refine Int.mul_le_mul_of_nonneg_left (by apply mul_le_mul <;> linarith) (by linarith)
        linarith
      have k1ork2 : k = 1 ∨ k = 2 := by omega
      -- Also $0 \leq k(y-z)^{2} \leq 1$, hence $k=2$ only if $y=z$. However then $y=z=1$,
      -- which is false in view of $y+z \geq 503$.
      have nk2 : k ≠ 2 := by
        intro k2
        simp [k2] at c3
        nlinarith
      tauto
    -- Combined with $k=1$ and $y+z=503 k$, this leads to $y=251, z=252$. 
    -- In summary the triple $(2,251,252)$ is the only solution.
    simp [k1] at c3
    replace c3 : y - z = -1 := (or_iff_right (by linarith)).1 c3
    simp [k1, c3] at hk
    split_ands <;> linarith
  -- Verify that the triple $(2,251,252)$ is solution.
  · simp [h]
