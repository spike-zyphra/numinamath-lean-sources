import Mathlib

open Polynomial

/- Given a polynomial p with real coefficients and the complex root a, then the complex conjugate of a is also a root. -/
lemma polynomial_roots_mem_star_of_mem {p : ℝ[X]} {a : ℂ} (hp : a ∈ p.aroots ℂ)
  : (starRingEnd ℂ) a ∈ p.aroots ℂ := by
  simpa only [mem_roots', Polynomial.map_eq_zero, IsRoot.def,
    eval_map_algebraMap, true_and, aeval_conj, map_eq_zero] using hp

/- A complex number equals a real number if it's complex conjugate equals the real number. -/
lemma complex_conj_eq_real {z : ℂ} {x : ℝ} (h : (starRingEnd ℂ) z = x)
  : z = x := by
    apply_fun ((starRingEnd ℂ) ·) at h
    rwa [RCLike.conj_conj, Complex.conj_ofReal] at h

/- Three elements in a multiset can be rotated. -/
lemma multiset_three_rotate {A : Type*} (x y z : A) : ({x, y, z} : Multiset A) = {y, z, x} := by
    simp only [Multiset.insert_eq_cons, ←Multiset.singleton_add, ←add_assoc]
    exact add_rotate _ _ _

/- Given three elements in a multiset, the last two elements commute -/
lemma multiset_three_right_comm {A : Type*} (x y z : A) : ({x, y, z} : Multiset A) = {x, z, y} := by
    simp only [Multiset.insert_eq_cons, ←Multiset.singleton_add, ←add_assoc]
    exact add_right_comm _ _ _

/- A cubic polynomial with non-zero discriminant has three roots all real or one real and
   two complex which are conjugates. -/
lemma complex_polynomial_roots_conj (p : Cubic ℝ) (hp : p.a ≠ 0) (hd : p.disc ≠ 0) :
  (∃ (a : ℂ) (b : ℝ), p.toPoly.aroots ℂ = {a, (starRingEnd ℂ) a, (b : ℂ)})
  ∨ (∃ (a b c : ℝ), p.toPoly.aroots ℂ = {(a : ℂ), (b : ℂ), (c : ℂ)}) := by

  -- the cubic has degree three
  have degree_eq_three : p.toPoly.natDegree = 3 := Cubic.natDegree_of_a_ne_zero hp

  -- so it has 3 complex roots
  have roots_card_eq_three : (p.toPoly.aroots ℂ).card = 3 := by
    rw [←degree_eq_three]
    refine (Polynomial.natDegree_eq_card_roots ?_).symm

    -- because every polynomial splits over ℂ
    exact IsAlgClosed.splits_codomain p.toPoly

  -- Call the three roots a, b and c
  obtain ⟨a, b, c, eq⟩ := Multiset.card_eq_three.mp roots_card_eq_three

  -- the roots are unique
  have ⟨ne1, ne2, ne3⟩ : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    rw [aroots, ←Cubic.map_toPoly] at eq
    refine (Cubic.disc_ne_zero_iff_roots_ne hp eq).mp hd

  -- a, b and c are all roots of p
  have a_mem : a ∈ p.toPoly.aroots ℂ := by norm_num [eq]
  have b_mem : b ∈ p.toPoly.aroots ℂ := by norm_num [eq]
  have c_mem : c ∈ p.toPoly.aroots ℂ := by norm_num [eq]

  -- so a*, b* and c* are also roots of p
  have a_star_mem := eq ▸ polynomial_roots_mem_star_of_mem a_mem
  have b_star_mem := eq ▸ polynomial_roots_mem_star_of_mem b_mem
  have c_star_mem := eq ▸ polynomial_roots_mem_star_of_mem c_mem

  -- then for x ∈ {a, b, c}, x* = a or b or c
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at a_star_mem b_star_mem c_star_mem

  -- so we have 3 * 3 * 3 = 27 possible situations

  -- but using symmetries we'll only need 4 situations

  -- all equal
  have case1 : ∀ {x y z : ℂ},
    (starRingEnd ℂ) x = x →
    (starRingEnd ℂ) y = y →
    (starRingEnd ℂ) z = z →
    ∃ ra rb rc: ℝ, x = ra ∧ y = rb ∧ z = rc := by
      intro x y z xh yh zh
      obtain ⟨rx, rfl⟩ := Complex.conj_eq_iff_real.mp xh
      obtain ⟨ry, rfl⟩ := Complex.conj_eq_iff_real.mp yh
      obtain ⟨rz, rfl⟩ := Complex.conj_eq_iff_real.mp zh
      exists rx, ry, rz

  -- none_equal, rotating
  have case2 : ∀ {x y z : ℂ},
    (starRingEnd ℂ) x = y →
    (starRingEnd ℂ) y = z →
    (starRingEnd ℂ) z = x →
    ∃ ra : ℝ, x = ra ∧ y = ra ∧ z = ra := by
      intro x y z xh yh zh
      rw [←zh] at xh
      simp only [RCLike.conj_conj] at xh
      subst xh
      obtain ⟨ry, rfl⟩ := Complex.conj_eq_iff_real.mp yh
      rw [Complex.conj_ofReal, Eq.comm] at zh
      exists ry

  -- one equal, other equal to eachother
  have case3 : ∀ {x y z : ℂ},
    (starRingEnd ℂ) x = x →
    (starRingEnd ℂ) y = z →
    (starRingEnd ℂ) z = y →
    ∃ (ra : ℝ) (zb : ℂ), x = ra ∧ y = zb ∧ z = (starRingEnd ℂ) zb := by
      intro x y z xh yh zh
      obtain ⟨rx, rfl⟩ := Complex.conj_eq_iff_real.mp xh
      exists rx, y
      exact ⟨rfl, rfl, yh.symm⟩

  -- none equal, two equal to eachother
  have case4 : ∀ {x y z : ℂ},
    (starRingEnd ℂ) x = y →
    (starRingEnd ℂ) y = x →
    (starRingEnd ℂ) z = x →
    z = y := by
      intro x y z xh yh zh
      simpa only [←zh, RCLike.conj_conj] using xh

  -- then we go through all 27 cases
  rcases a_star_mem with eq_a | eq_b | eq_c
  · rcases b_star_mem with eq_a2 | eq_b2 | eq_c2
    · exact False.elim (ne1.symm (case4 eq_a eq_a eq_a2))
    · rcases c_star_mem with eq_a3 | eq_b3 | eq_c3
      · exact False.elim (ne2.symm (case4 eq_a eq_a eq_a3))
      · exact False.elim (ne3.symm (case4 eq_b2 eq_b2 eq_b3))
      · obtain ⟨ra, rb, rc, rfl, rfl, rfl⟩ := case1 eq_a eq_b2 eq_c3
        right
        exists ra, rb, rc
    · rcases c_star_mem with eq_a3 | eq_b3 | eq_c3
      · exact False.elim (ne2.symm (case4 eq_a eq_a eq_a3))
      · obtain ⟨ra, zb, rfl, rfl, rfl⟩ := case3 eq_a eq_c2 eq_b3
        left
        exists b, ra
        exact eq ▸ multiset_three_rotate _ _ _
      · exact False.elim (ne3 (case4 eq_c3 eq_c3 eq_c2))
  · rcases b_star_mem with eq_a2 | eq_b2 | eq_c2
    · rcases c_star_mem with eq_a3 | eq_b3 | eq_c3
      · exact False.elim (ne3.symm (case4 eq_b eq_a2 eq_a3))
      · exact False.elim (ne2.symm (case4 eq_a2 eq_b eq_b3))
      · obtain ⟨ra, zb, rfl, rfl, rfl⟩ := case3 eq_c3 eq_b eq_a2
        left
        exists a, ra
    · exact False.elim (ne1 (case4 eq_b2 eq_b2 eq_b))
    · rcases c_star_mem with eq_a3 | eq_b3 | eq_c3
      · obtain ⟨ra, rfl, rfl, rfl⟩ := case2 eq_b eq_c2 eq_a3
        right
        exists ra, ra, ra
      · exact False.elim (ne2 (case4 eq_c2 eq_b3 eq_b))
      · exact False.elim (ne3 (case4 eq_c3 eq_c3 eq_c2))
  · rcases c_star_mem with eq_a3 | eq_b3 | eq_c3
    · rcases b_star_mem with eq_a2 | eq_b2 | eq_c2
      · exact False.elim (ne3 (case4 eq_c eq_a3 eq_a2))
      · obtain ⟨ra, zb, rfl, rfl, rfl⟩ := case3 eq_b2 eq_c eq_a3
        left
        exists a, ra
        exact eq ▸ multiset_three_right_comm _ _ _
      · exact False.elim (ne1.symm (case4 eq_a3 eq_c eq_c2))
    · rcases b_star_mem with eq_a2 | eq_b2 | eq_c2
      · obtain ⟨ra, rfl, rfl, rfl⟩ := case2 eq_c eq_b3 eq_a2
        right
        exists ra, ra, ra
      · exact False.elim (ne3.symm (case4 eq_b2 eq_b2 eq_b3))
      · exact False.elim (ne1 (case4 eq_b3 eq_c2 eq_c))
    · exact False.elim (ne2 (case4 eq_c3 eq_c3 eq_c))

/- The roots of a polynomial are equal to some set if they're equal across a ring homomorphisms. -/
lemma map_roots_eq_map {P : ℝ[X]} {S : Multiset ℝ} {f : ℝ →+* ℂ} (h : (P.map f).roots = Multiset.map f S)
: P.roots = S := by
    ext i
    rw [Polynomial.count_roots, Polynomial.eq_rootMultiplicity_map f.injective,
      ←Polynomial.count_roots, h, Multiset.count_map_eq_count']
    exact f.injective

/- A cubic polynomial with real coefficients and positive discriminant has three unique real roots. -/
lemma real_cubic_unique_roots_of_disc_pos (p : Cubic ℝ) (ph : p.a ≠ 0) (h : 0 < p.disc) :
  ∃ a b c, p.toPoly.roots = {a, b, c} ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a := by
    -- the discriminant is non-zero
    have disc_ne_zero : p.disc ≠ 0 := by linarith

    -- so we have two cases of possible roots
    rcases complex_polynomial_roots_conj p ph disc_ne_zero with ⟨z, x, hh⟩ | ⟨a, b, c, hh⟩
    -- one root is real and other two are complex conjugates
    · convert_to (Cubic.map (algebraMap ℝ ℂ) p).toPoly.roots = ({z, (starRingEnd ℂ) z, (x : ℂ)} : Multiset ℂ) at hh
      · rw [Cubic.map_toPoly]
      have disc_eq := Cubic.disc_eq_prod_three_roots ph hh
      norm_num at disc_eq

      -- we consider the cases where some roots are equal

      -- let z = x
      by_cases hx : z = x
      -- then the discriminant is equal to zero
      · have eq_zero : p.disc = 0 := by
          simpa only [hx, Complex.conj_ofReal, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, Complex.ofReal_eq_zero] using disc_eq
        -- but the discriminant is positive, contradiction
        linarith

      -- let z* = x
      by_cases hx' : (starRingEnd ℂ) z = x
      -- then the discriminant is equal to zero
      · have eq_zero : p.disc = 0 := by
          simpa only [hx', sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            zero_pow, Complex.ofReal_eq_zero] using disc_eq
        -- but the discriminant is positive, contradiction
        linarith

      -- we simplify the discriminant

      -- two factors are complex conjugates of each other
      have conj_eq : (starRingEnd ℂ) (z - ↑x) = ((starRingEnd ℂ) z - ↑x) := by
        simp only [map_sub, Complex.conj_ofReal]

      rw [←conj_eq, Complex.sub_conj, mul_assoc _ _ ((starRingEnd ℂ) (z - ↑x)),
        Complex.mul_conj] at disc_eq

      -- we can see that the discriminant is non-positive
      have nonpos_disc : (p.disc : ℂ).re ≤ 0 := by
        rw [disc_eq, pow_two]

        -- simplify
        simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re,
          Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, zero_add, zero_sub,
          Left.neg_nonpos_iff]

        -- we have 0 ≤ "a bunch of even powers"
        ring_nf
        -- and even powers are always non-negative
        positivity

      -- so the discriminant is non-positive
      simp only [Complex.ofReal_re] at nonpos_disc

      -- but discriminant is positive, contradiction
      linarith

    -- all three roots are real
    · exists a, b, c
      unfold Polynomial.aroots at hh
      constructor
      -- then the polynomial (regarded as a real polynomial) has the roots a, b and c
      · have map_eq : ({a, b, c} : Multiset ℝ).map (algebraMap ℝ ℂ) = ({(a : ℂ), (b : ℂ), (c : ℂ)} : Multiset ℂ) := by norm_num
        exact map_roots_eq_map (map_eq ▸ hh)
      -- and each root is pairwise non-equal
      · convert_to (Cubic.map (algebraMap ℝ ℂ) p).toPoly.roots = ({(a : ℂ), (b : ℂ), (c : ℂ)} : Multiset ℂ) at hh
        · rw [Cubic.map_toPoly]
        -- because the discriminant is not zero
        have roots_nodup := (Cubic.disc_ne_zero_iff_roots_nodup ph hh).mp disc_ne_zero
        rw [Cubic.roots, hh] at roots_nodup
        norm_num at roots_nodup
        tauto

/- A multiset with three elements has no duplicates if each pair is non-equal -/
lemma multiset_nodup_three_of_ne {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
  ({a, b, c} : Multiset ℝ).Nodup := by
    norm_num
    tauto

/- If x is a root of p and q, then x is a root of (p - q). -/
lemma polynomial_root_sub_of_root_of_root {p q : ℝ[X]} {x : ℝ}
  (hp : p.IsRoot x) (hq : q.IsRoot x) :
  (p - q).IsRoot x := by
    simp only [IsRoot.def] at hp hq
    rw [IsRoot.def, eval_sub, hp, hq, zero_sub_zero]

/- Let $f(x)=x^{2}-2$. Prove that the equation $f(f(f(x)))=x$ has eight distinct real solutions. -/
theorem algebra_177012 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 2) :
    Set.ncard {x | f (f (f x)) = x} = 8 := by
    -- Let P1, P2, P3, P4 be the factors of P = (f (f (f x)) - x)
    let P1 : ℝ[X] := (X + C (-2))
    let P2 : ℝ[X] := (X + C 1)
    let P3 : ℝ[X] := (X ^ 3 + C (-3) * X + C 1)
    let P4 : ℝ[X] := (X ^ 3 + X ^ 2 + (C (-2)) * X + (C (-1)))
    let P : ℝ[X] := P1 * P2 * P3 * P4

    -- P is not zero
    have P_ne_zero : P ≠ 0 := by
      unfold P P1 P2 P3 P4
      simp only [ne_eq, mul_eq_zero, not_or]
      split_ands
      all_goals
      · apply_fun (coeff · 0)
        norm_num

    -- the set we want to find the cardinality of, is equal to the (unique) roots of P
    have set_eq_roots : {x | f (f (f x)) = x} = P.roots.toFinset := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots', ne_eq,
        P_ne_zero, not_false_eq_true, IsRoot.def, true_and]
      unfold P P1 P2 P3 P4
      simp only [map_neg, map_one, neg_mul, eval_mul, eval_add, eval_X, eval_neg, eval_C, eval_one,
        eval_pow]

      rw [hf]
      ring_nf
      constructor
      all_goals
      · intro aa
        linarith

    rw [set_eq_roots]

    -- first factor has one unique root: 2
    have P1_roots : P1.roots = {2} := by
      simp only [P1, Polynomial.roots_X_add_C, Int.reduceNeg, neg_neg]

    -- second factor has one unique root: -1
    have P2_roots : P2.roots = {-1} := by
      simp only [P2, Polynomial.roots_X_add_C, Int.reduceNeg, neg_neg]

    -- third factor has three unique roots. Call them a, b, c
    obtain ⟨a, b, c, P3_roots, ne1, ne2, ne3⟩ :
      ∃ a b c, P3.roots = {a, b, c}
        ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a := by
      -- let the cubic be 1 * x ^ 3 + 0 * x ^ 2 + (-3) * x + 1
      let cube : Cubic ℝ := { a := 1, b := 0, c := -3, d := 1 }

      -- it's equal to our simplified form
      have cubic_to_cube_eq : P3 = cube.toPoly := by
        unfold Cubic.toPoly P3
        norm_num

      -- the discriminant is positive
      have disc_pos : 0 < cube.disc := by
        unfold Cubic.disc
        norm_num

      -- leading coefficient is not zero
      have a_ne_zero : cube.a ≠ 0 := (zero_ne_one' ℝ).symm

      convert real_cubic_unique_roots_of_disc_pos cube a_ne_zero disc_pos

    -- fourth factor has three unique roots. Call them d, e, f
    obtain ⟨d, e, f, P4_roots, ne4, ne5, ne6⟩ :
      ∃ a b c, P4.roots = {a, b, c}
        ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a := by
      -- let the cubic be 1 * x ^ 3 + 1 * x ^ 2 + (-2) * x + (-1)
      let cube : Cubic ℝ := { a := 1, b := 1, c := -2, d := -1 }

      -- it's equal to our simplified form
      have cubic_to_cube_eq : P4 = cube.toPoly := by
        norm_num [Cubic.toPoly, P4]

      -- the discriminant is positive
      have disc_pos : 0 < cube.disc := by
        norm_num [Cubic.disc]

      -- leading coefficient is not zero
      have a_ne_zero : cube.a ≠ 0 := (zero_ne_one' ℝ).symm

      -- if the discriminant is positive, the result follows
      convert real_cubic_unique_roots_of_disc_pos cube a_ne_zero disc_pos

    -- the roots of P is the union of the roots of it's factors: P1, P2, P3, P4
    have P_roots_eq : P.roots = P1.roots + P2.roots + P3.roots + P4.roots := by
      unfold P
      iterate 3 rw [Polynomial.roots_mul]
      -- none of the factors is zero
      all_goals
      · simp only [P1, P2, P3, P4]
        apply_fun (coeff · 0)
        norm_num

    -- P has 8 roots (which may include duplicates)
    have roots_card : P.roots.card = 8 := by
      simp only [P_roots_eq, Multiset.card_add, P1_roots, P2_roots, P3_roots, P4_roots]
      norm_num

    -- but P has no duplicates
    have roots_nodup : P.roots.Nodup := by
      rw [P_roots_eq]
      simp [Multiset.nodup_add]
      split_ands
      -- P1 has no duplicate roots
      · exact P1_roots ▸ Multiset.nodup_singleton 2
      -- P2 has no duplicate roots
      · exact P2_roots ▸ Multiset.nodup_singleton (-1)
      -- the roots of P1 and P2 are disjoint
      · rw [P1_roots, P2_roots]
        norm_num
      -- P3 has no duplicate roots
      · exact P3_roots ▸ multiset_nodup_three_of_ne ne1 ne2 ne3
      -- the roots of P1 and P3 are disjoint
      · rw [P1_roots, Multiset.singleton_disjoint]
        simp only [P3, mem_roots', IsRoot.def]
        norm_num
      -- the roots of P2 and P3 are disjoint
      · rw [P2_roots, Multiset.singleton_disjoint]
        simp only [P3, mem_roots', IsRoot.def]
        norm_num
      -- P4 has no duplicate roots
      · exact P4_roots ▸ multiset_nodup_three_of_ne ne4 ne5 ne6
      -- the roots of P1 and P4 are disjoint
      · rw [P1_roots, Multiset.singleton_disjoint]
        simp only [P4, mem_roots', IsRoot.def]
        norm_num
      -- the roots of P2 and P4 are disjoint
      · rw [P2_roots, Multiset.singleton_disjoint]
        simp only [P4, mem_roots', IsRoot.def]
        norm_num
      -- the roots of P3 and P4 are disjoint
      -- assume opposite
      · by_contra not_disjoint

        -- then there is some root x which is a root of both P3 and P4
        obtain ⟨x, P3_is_root, P4_is_root⟩ : ∃ x, P3.IsRoot x ∧ P4.IsRoot x := by
          have mem_exists := Multiset.disjoint_iff_ne.mpr.mt not_disjoint
          simp only [not_forall, Decidable.not_not] at mem_exists
          obtain ⟨x, hx, y, hy, rfl⟩ := mem_exists
          have P3_is_root : P3.IsRoot x := isRoot_of_mem_roots hx
          have P4_is_root : P4.IsRoot x := isRoot_of_mem_roots hy
          exists x

        -- so x is also a root of P4 - P3
        have sub_root := polynomial_root_sub_of_root_of_root P4_is_root P3_is_root

        -- normalize P3...
        have P3_normal : P3 = C 1 * X ^ 3 + C 0 * X ^ 2 + C (-3) * X + C 1 := by
            unfold P3
            norm_num

        -- ...and P4
        have P4_normal : P4 = C 1 * X ^ 3 + C 1 * X ^ 2 + C (-2) * X + C (-1) := by
            unfold P4
            norm_num

        -- then we can see that P4 - P3 = x^2 + x - 2
        have eq : P4 - P3 = X ^ 2 + X + C (-2) := by
          -- rhs degree is less than 3
          have rhs_degree : (X ^ 2 + X + C (-2) : ℝ[X]).natDegree ≤ 3 := by
            convert_to (C 1 * X ^ 2 + C 1 * X + C (-2) : ℝ[X]).natDegree ≤ 3
            norm_num
            rw [Polynomial.natDegree_quadratic (by linarith)]
            omega

          -- lhs degree is less than 3
          have lhs_degree : (P4 - P3).natDegree ≤ 3 := by
            refine (Polynomial.natDegree_sub_le_iff_left ?_).mpr ?_
            · rw [P3_normal, Polynomial.natDegree_cubic (by linarith)]
            · rw [P4_normal, Polynomial.natDegree_cubic (by linarith)]

          -- so we just need to check that both sides are equal at coefficients for x^i where i ≤ 3
          refine (Polynomial.ext_iff_natDegree_le lhs_degree rhs_degree).mpr ?_
          intro i ih
          unfold P3 P4
          interval_cases i
          -- coefficient of x^0 is equal
          · norm_num
          -- coefficient of x^1 is equal
          · norm_num [-map_one]
          -- coefficient of x^2 is equal
          · norm_num [-map_one, Polynomial.coeff_X]
          -- coefficient of x^3 is equal
          · norm_num [-map_one, Polynomial.coeff_X]

        -- the we have x^2 + x - 2 = 0
        convert_to 1 * (x * x) + 1 * x + (-2) = 0 using 0 at sub_root
        · norm_num [eq]
          ring_nf

        -- the discriminant is equal to 3 * 3
        have discrim_eq : discrim (1 : ℝ) 1 (-2) = 3 * 3 := by norm_num [discrim]

        -- we have that x = 1 or -2
        have roots := (quadratic_eq_zero_iff (by linarith) discrim_eq x).mp sub_root
        norm_num at roots

        -- but in both cases, x can't have been a root of P3, contradiction
        rcases roots with rfl | rfl
        · norm_num [P3] at P3_is_root
        · norm_num [P3] at P3_is_root

    -- so we have 8 unique roots
    simp only [←roots_card, Set.ncard_eq_toFinset_card', Finset.toFinset_coe,
      Multiset.toFinset_card_of_nodup roots_nodup]