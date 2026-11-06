import Mathlib
set_option maxHeartbeats 99999999999999
/- Determine all functions $f$ defined on the set of all positive integers and taking non-negative integer values, satisfying the three conditions: (i) $f(n) \neq 0$ for at least one $n$; (ii) $f(x y)=f(x)+f(y)$ for every positive integers $x$ and $y$; (iii) there are infinitely many positive integers $n$ such that $f(k)=f(n-k)$ for all $k<n$. (Croatia) -/
theorem number_theory_24028 :
    {f : ℕ → ℕ | (f 0 = 0) ∧ (∀ x y, 0 < x → 0 < y → f (x*y) = f x + f y) ∧
      {n | 0 < n ∧ ∀ k < n, 0 < k → f k = f (n - k)}.Infinite} = {f | ∃ c p, Nat.Prime p ∧ f = fun x => c * Nat.factorization x p } := by
  ext f
  simp only [Set.mem_setOf_eq]
  symm; constructor
  -- the function satisfies the conditions
  · intro q
    obtain ⟨c, p, h1, h2⟩ := q
    -- we solve the f 0 = 0
    simp only [h2, Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, mul_zero,
      mul_eq_mul_left_iff, true_and]
    constructor
    -- it is multiplicative
    · intros x y hx hy
      rw [Nat.factorization_mul (by exact Nat.not_eq_zero_of_lt hx) (by aesop)]
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring
    -- many good n values
    · rw [← Set.infinite_coe_iff]
      apply Infinite.of_injective (fun (m : ℕ) => ⟨p^m, by {
        simp only [Set.mem_setOf_eq]
        constructor
        -- p^m is positive
        · have p1 : 0 < p := by exact Nat.Prime.pos h1
          obtain _ | m := m
          · norm_num
          have s := Nat.pow_lt_pow_left p1 (n := m + 1) (by norm_num)
          norm_num at s
          exact s
        -- ∀ k < p ^ m, k.factorization p = (p ^ m - k).factorization p ∨ c = 0
        · intros y hy hb
          have mm : y = p^(y.factorization p) * (y / (p^(y.factorization p))) := by
            have th := Nat.ordProj_dvd y p
            obtain ⟨nn, hh⟩ := th
            conv =>
              rhs
              right; left; rewrite [hh]
            have dd (k : ℕ) : 0 < p^k := by
              obtain _ | k := k
              · norm_num
              have s := Nat.pow_lt_pow_left (Nat.Prime.pos h1) (n := k + 1) (by norm_num)
              norm_num at s; exact s
            rw [Nat.mul_div_cancel_left]; · exact hh
            · apply dd
          conv =>
            left; rhs; rw [mm]
          have hj : y ≤ p^m := by exact Nat.le_of_succ_le hy
          have gy := Nat.factorization_le_of_le_pow hj
          conv =>
            left; rhs; left; rw [(by omega : m = (m - y.factorization p) + y.factorization p)]
            rw [Nat.pow_add, Nat.mul_comm, ← Nat.mul_sub]
          -- we ought to prove (p ^ (m - y.factorization p) - y / p ^ y.factorization p) is not divisible by p
          have dd (k : ℕ) : 0 < p^k := by
            obtain _ | k := k
            · norm_num
            have s := Nat.pow_lt_pow_left (Nat.Prime.pos h1) (n := k + 1) (by norm_num)
            norm_num at s; exact s
          have j1 := dd (y.factorization p)
          -- yeah that was a setup
          -- what if y = 0
          have nm : y.factorization p ≠ m := by
            intro ct
            have hh := Nat.ordProj_mul_ordCompl_eq_self y p
            simp only [ct] at hh
            have nn := @Nat.ordCompl_pos y p (by exact Nat.not_eq_zero_of_lt hb)
            rw [ct] at nn
            clear h2 f c mm j1 ct gy
            -- now this is arithmetic
            have hp : 0 < p ^ m := dd m

            have hge1 : y / p ^ m ≥ 1 := by linarith

            have h4 : y ≥ p ^ m := by
              have eq1 : p ^ m * (y / p ^ m) = y := by linarith [hh]
              have hmul : p ^ m * (y / p ^ m) ≥ p ^ m * 1 := by
                nlinarith [hge1, hp]
              have eq2 : y = p ^ m * (y / p ^ m) := by linarith [eq1]
              linarith [eq2, hmul]

            linarith [hy, h4]
          have jfk : ¬ p ∣ (p ^ (m - y.factorization p) - y / p ^ y.factorization p) := by
            -- not divisible
            have kk := @Nat.not_dvd_ordCompl y p h1 (by clear * - hb; aesop)
            have qr : p ∣ p ^ (m - y.factorization p) := by
              rw [(by omega : m - y.factorization p = (m - y.factorization p - 1) + 1)]
              rw [Nat.pow_add]; norm_num
            have y_eq : y = p ^ y.factorization p * (y / p ^ y.factorization p) := by exact mm
            have y_le : y ≤ p ^ m := by exact hj
            rw [y_eq] at y_le
            have pos_p_k : 0 < p ^ y.factorization p := by exact j1
            -- prove inequality
            have n_le : y / p ^ y.factorization p ≤ p ^ (m - y.factorization p) := by
              have H1 : p ^ y.factorization p * (y / p ^ y.factorization p) ≤ p ^ m := by
                  exact y_le
              have pos1 : 0 < p ^ y.factorization p := by exact j1
              have H2 : y / p ^ y.factorization p ≤ p ^ m / (p ^ y.factorization p) := by
                  apply Nat.div_le_div
                  all_goals linarith
              have H3 : p ^ m / (p ^ y.factorization p) = p ^ (m - y.factorization p) := by
                  rw [Nat.pow_div]
                  · assumption
                  · exact Nat.pos_of_dvd_of_pos qr (dd (m - y.factorization p))
              linarith [H2, H3]
            intro cc
            -- subtract two divisibility statements 
            have uu := Nat.dvd_sub (by apply Nat.sub_le) qr cc
            rw [Nat.sub_sub_self n_le] at uu
            exact kk uu
          left
          have jh
            (a b : ℕ)
            (h₀ : ¬ a ∣ b) :
            b ≠ 0 := by
            by_contra h
            have h₁ : a ∣ b := by 
              rw [h]
              use 0
              simp
            contradiction
          -- conclude it is good
          have re := jh _ _ jfk
          rw [Nat.factorization_mul (by exact Ne.symm (Nat.ne_of_lt (dd (y.factorization p)))) re]
          simp only [Nat.factorization_pow, h1, Nat.Prime.factorization, Finsupp.smul_single,
            smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
            self_eq_add_right]
          apply Nat.factorization_eq_zero_of_not_dvd
          exact jfk
      }⟩)
      intros aa bb hab
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq] at hab
      have he : 2 ≤ p := by exact Nat.Prime.two_le h1
      clear h2 h1 c f
      apply Nat.pow_right_injective
      · exact he
      · exact hab
  · intro h
    obtain ⟨a, b, c⟩ := h
    -- f 1 = 0
    have fo : f 1 = 0 := by
      have qq := b 1 1 (by decide) (by decide)
      norm_num at qq
      nlinarith
    -- trivial case: f is 0 on all primes
    by_cases tr : ∀ x, Nat.Prime x → f x = 0
    · have st x : f x = 0 := by
        -- induction on prime factorization
        induction' x using induction_on_primes with p aa hp ih
        · exact a
        · exact fo
        · obtain _ | aa := aa
          -- when aa = 0
          · norm_num; exact a
          -- nonzero
          · rw [b _ _ (by exact Nat.Prime.pos hp) (by norm_num)]
            rw [tr _ hp, Nat.zero_add]; exact ih
      -- now we know f is 0 everywhere
      exists 0, 2
      constructor
      · decide
      simp only [zero_mul]
      ext x
      apply st
    · push_neg at tr
      -- time to pull an infinite descent to get smallest prime p such that f p = 0
      have ex : ∃ x, IsLeast { x | Nat.Prime x ∧ f x ≠ 0 } x := by
        clear * - tr
        obtain ⟨w, tr, rr⟩ := tr
        use Nat.find (show ∃ x, Nat.Prime x ∧ f x ≠ 0 by
          exact ⟨w, tr, rr⟩)
        constructor
        · -- Show that the element is in the set
          show Nat.Prime (Nat.find (show ∃ x, Nat.Prime x ∧ f x ≠ 0 by
            exact ⟨w, tr, rr⟩)) ∧ f (Nat.find (show ∃ x, Nat.Prime x ∧ f x ≠ 0 by
            exact ⟨w, tr, rr⟩)) ≠ 0
          exact Nat.find_spec (show ∃ x, Nat.Prime x ∧ f x ≠ 0 by
            exact ⟨w, tr, rr⟩)
        · -- Show that the element is the least in the set
          intro y hy
          have h1 : Nat.Prime y := hy.1
          have h2 : f y ≠ 0 := hy.2
          have h3 : Nat.find (show ∃ x, Nat.Prime x ∧ f x ≠ 0 by
            exact ⟨w, tr, rr⟩) ≤ y := by
            apply Nat.find_le
            exact ⟨h1, h2⟩
          linarith
      clear tr
      obtain ⟨x, tr, rr⟩ := ex
      simp only [ne_eq, Set.mem_setOf_eq, mem_lowerBounds, and_imp] at tr rr
      exists f x, x
      -- f k = 0 for all primes k less than x
      have zb k (hk : k < x) (pp : Nat.Prime k) : f k = 0 := by
        have dr := rr k pp
        have fk : ¬(x ≤ k) := by exact Nat.not_le_of_lt hk
        tauto
      -- f k = 0 for all k less than x
      have zb1 k (hk : k < x) : f k = 0 := by
        -- induction on prime factorization
        induction' k using induction_on_primes with p aa hp ih
        · exact a
        · exact fo
        · obtain _ | aa := aa
          -- when aa = 0
          · norm_num; exact a
          -- nonzero
          · have jn : 2 ≤ p := by exact Nat.Prime.two_le hp
            rw [b _ _ (by exact Nat.zero_lt_of_lt jn) (by norm_num)]
            rw [zb _ (by nlinarith) hp]
            rw [ih (by nlinarith)]
      obtain ⟨tr, tt⟩ := tr
      constructor; · exact tr
      /-
      * **Good divisors remain good.**
      If $n$ is good and $d\mid n$, say $n=d\,m$, then for $0<k<d$:

      $$
        f(k)
        = f(mk)-f(m)
        = f\bigl(n-mk\bigr)-f(m)
        = f\bigl(m(d-k)\bigr)-f(m)
        = f(d-k),
      $$

      so $d$ is good too.
      -/
      have rg n (g1 : 0 < n) (g2 : ∀ k < n, 0 < k → f k = f (n - k)) d (hd : d ∣ n) : ∀ k < d, 0 < k → f k = f (d - k) := by
        intros k hk kh
        obtain ⟨m, hm⟩ := hd
        have rj := g2 (m * k) (by nlinarith) (by nlinarith)
        rw [b _ _ (by nlinarith) (by nlinarith)] at rj -- we decompose
        rw [hm] at rj
        -- now we use distributive property 
        rw [(by clear * -; rw [Nat.mul_sub]; ring_nf : (d * m - m * k) = m * (d - k))] at rj
        have fk : 0 < d - k := by omega
        rw [b _ _ (by nlinarith) fk] at rj
        -- cancel terms
        clear * - rj; omega
      -- a tiny fact:
      have dh : 2 ≤ x := by exact Nat.Prime.two_le tr
      -- any good n > x is divisible by x
      have me n (g1 : x < n) (g2 : ∀ k < n, 0 < k → f k = f (n - k)) : x ∣ n := by
        -- for the sake of contradiction
        by_contra h
        -- use x * (n / x)
        have dw : 0 < n / x := by
          apply Nat.div_pos <;> linarith
        -- we get f (x * (n / x)) = f (n - x * (n / x))
        have g3 := g2 (x * (n / x)) (by exact Nat.mul_div_lt_iff_not_dvd.mpr h) (by nlinarith)
        -- now apply the multiplication formula
        rw [b _ _ (by nlinarith) (by nlinarith)] at g3
        have lil : n - x * (n / x) < x := by
          clear * - dh
          rw [← Nat.mod_def]
          apply Nat.mod_lt
          linarith
        -- from this derive that right hand side is 0
        rw [zb1 _ lil] at g3
        clear * - g3 tt
        -- we have a clear contradiction
        omega
      have plk
          (T : Set ℕ)
          (hT : Infinite T)
          (n : ℕ)
          : ∃ w ∈ T, w ≥ n := by 
        by_contra h
        push_neg at h
        
        have h1 : T ⊆ Set.Iio n := by 
          intro w hw
          have h2 : w < n := h w hw
          exact Set.mem_Iio.mpr h2
        
        have h2 : Finite T := by 
          apply Set.Finite.subset
          · exact Set.finite_Iio n
          · exact h1
        
        have h3 : ¬Infinite T := by 
          simpa using h2
        
        contradiction
      have alx := plk {n | 0 < n ∧ ∀ k < n, 0 < k → f k = f (n - k)} (Set.infinite_coe_iff.mpr c)
      simp only [Set.mem_setOf_eq, ge_iff_le] at alx
      let good := {n | 0 < n ∧ ∀ k < n, 0 < k → f k = f (n - k)}
      -- every good number has the form r * x^j
      have form n (hh : good n) : ∃ r j, r < x ∧ n = r * x^j := by
        -- we set up an isolated environment
        have rs n1 (hd : n1 ∣ n) : good n1 := by
          unfold good
          simp only [setOf]
          unfold good at hh
          simp only [setOf] at hh
          constructor
          · obtain ⟨hh, nn⟩ := hh
            obtain ⟨uu, hd⟩ := hd
            clear * - hh hd
            nlinarith
          · apply rg
            · exact hh.2
            · exact hd
            · exact hh.1
        -- another piece of the environment
        have rt n1 (hd : good n1) (hll : x < n1) : x ∣ n1 := by
          unfold good at hd
          simp only [setOf] at hd
          apply me
          · exact hll
          · tauto
        clear * - rs rt tr hh
        by_cases iz : n = 0
        · rw [iz]
          exists 0, 0
          simp only [pow_zero, mul_one, and_true]
          clear * - tr
          exact Nat.Prime.pos tr
        exists n / x^(n.factorization x), (n.factorization x)
        constructor
        · have dv := @Nat.ordCompl_dvd n x
          -- r is good
          have gd := rs _ dv
          have ts := rt _ gd
          have imm : ¬x ∣ n / x ^ n.factorization x := @Nat.not_dvd_ordCompl n x tr iz
          have mnr : ¬x < n / x ^ n.factorization x := by tauto
          have nq : x ≠ n / x ^ n.factorization x := by
            intro cntr
            have mdx := @Nat.not_dvd_ordCompl n x tr iz
            rw [←cntr] at mdx
            simp only [dvd_refl, not_true_eq_false] at mdx
          omega
        · have xnd := @Nat.ordProj_dvd n x
          obtain ⟨xnd, dxx⟩ := xnd
          conv =>
            rhs; left; left; rw [dxx]
          rw [Nat.mul_div_cancel_left _ (by apply Nat.pow_pos; exact Nat.Prime.pos tr)]
          rw [Nat.mul_comm, ← dxx]
      -- implement GetLargeWitness
      have GetLargeWitness (k : ℕ) : ∃ m, good (x ^ m) ∧ k ≤ m := by
        unfold good
        simp only [setOf]
        -- call alx with x^k
        obtain ⟨ik, ⟨rf, ui⟩⟩ := alx (x^k)
        have ⟨bb, cc, oo⟩ := form _ rf
        -- cc is what we're looking for
        exists cc
        constructor
        · constructor
          · apply Nat.pow_pos
            exact Nat.Prime.pos tr
          · -- x^cc is a divisor of ik, so x^cc is good
            exact rg ik (by tauto) rf.2 (x^cc) (by rw [oo.2]; simp)
        · -- since x^cc ≤ x^k, we have cc ≤ k
          have slx : ik < x * x ^ cc := by
            obtain ⟨oo, ooo⟩ := oo
            rw [ooo]
            have ppos := Nat.Prime.pos tr
            apply Nat.mul_lt_mul_of_pos_right
            · exact oo
            · apply Nat.pow_pos
              exact ppos
          rw [(by rw [Nat.pow_add]; norm_num; ring : x * x ^ cc = x ^ (cc + 1))] at slx
          have xsx : x ^ k < x ^ (cc + 1) := by
            clear * - ui slx
            linarith
          rw [Nat.pow_lt_pow_iff_right (by clear * - dh; omega)] at xsx
          clear * - xsx; omega
      have ag r : ∀ k < x^r, 0 < k → f k = f (x^r - k) := by
        intros k hk
        have ⟨m, ⟨go, gg⟩⟩ := GetLargeWitness r
        exact rg (x^m) (by apply Nat.pow_pos; exact Nat.Prime.pos tr) go.2 (x^r) (by apply Nat.pow_dvd_pow; exact gg) _ hk
      -- now all powers of x are good
      -- now prove that for all prime y ≠ x, f y = 0
      have bad (y : ℕ) (hp : Nat.Prime y) (hy : y ≠ x) : f y = 0 := by
        have fc : 1 < x^(y - 1) := by {
          have xs := Nat.Prime.two_le hp
          clear * - xs dh
          have h2 : 1 < x := by omega
          have h3 : y - 1 > 0 := by omega
          apply Nat.one_lt_pow 
          all_goals omega
        }
        have fn := ag (y - 1) 1 fc (by norm_num)
        -- f (x ^ (y - 1) - 1) = 0
        rw [fo] at fn; symm at fn
        have eye := Nat.coprime_pow_primes 1 1 hp tr hy
        norm_num at eye
        have xls := @Nat.ModEq.pow_totient x y (Nat.Coprime.symm eye)
        simp only [Nat.totient_prime hp] at xls
        rw [←Int.natCast_modEq_iff] at xls
        have xns := Int.ModEq.sub_right 1 xls
        norm_num at xns
        -- now cast back
        have sbx : (↑x ^ (y - 1) - 1 : ℤ) = (↑(x ^ (y - 1) - 1)) := by
          have xkw : 1 ≤ x^(y - 1) := by
            apply Nat.one_le_pow
            exact Nat.Prime.pos tr
          zify [xkw]
        rw [sbx, (by norm_num : (0 : ℤ) = (0 : ℕ))] at xns
        rw [Int.natCast_modEq_iff, Nat.modEq_zero_iff_dvd] at xns
        -- final
        obtain ⟨xns, snx⟩ := xns
        rw [snx, b _ _ (by nlinarith) (by nlinarith)] at fn
        clear * - fn
        omega
      ext u
      -- we now know the core properties of the function
      -- we now do induction on the prime factorization of u
      induction' u using induction_on_primes with p aa hp ih
      · simp [a]
      · simp [fo]
      · obtain _ | aa := aa
        · simp [a]
        rw [b _ _ (Nat.Prime.pos hp) (by norm_num)]
        rw [Nat.factorization_mul (Nat.Prime.ne_zero hp) (by norm_num)]
        simp only [ih, Finsupp.coe_add, Pi.add_apply]
        -- now we do a case split
        by_cases et : p = x
        · subst p
          rw [Nat.Prime.factorization_self hp]
          ring
        -- if p is not equal to x
        · rw [bad _ hp et]
          have za : p.factorization x = 0 := by
            rw [Nat.factorization_eq_zero_iff]
            right; left
            have eye := Nat.Coprime.symm (Nat.coprime_pow_primes 1 1 hp tr et)
            norm_num at eye
            rw [Nat.Prime.coprime_iff_not_dvd tr] at eye
            exact eye
          rw [za]
          ring
