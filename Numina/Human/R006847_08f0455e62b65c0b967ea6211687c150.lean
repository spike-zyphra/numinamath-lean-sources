import Mathlib


/-! # Units of `ZMod (p^k)` and `ZMod (2 * p ^ k)` are cyclic for odd p

If `p` is an odd prime, then the units of `ZMod (p^k)` and `ZMod (2 * p ^ k)` are cyclic.

-/


theorem primitive_root_modulo_n {p k : ℕ} [hp : Fact (Nat.Prime p)] (hp1 : Odd p) (hk : 0 < k)
  :IsCyclic (ZMod (p ^ k))ˣ ∧ IsCyclic (ZMod (2 * p ^ k))ˣ := by

  -- lemma: if p - 1 ∣ n ∣ p^(k-1)*(p-1), then n = p^j * (p - 1) for some j ≤ k - 1
  have exists_pow_mul :∀(p k n : ℕ),
  (hp : p.Prime) → (hk : 1 ≤ k) →
  (h1 : p - 1 ∣ n)→
  (h2 : n ∣ p^(k - 1) * (p - 1)) →
  ∃ j ≤ k - 1, n = p^j * (p - 1) := by
    intro p k n hp hk h1 h2

    have h_p_gt_1: p>1 := by exact Nat.Prime.one_lt hp
    have h_p_pow: p^(k - 1) > 0 := by
      calc
        _ ≥ p ^ 0 := Nat.pow_le_pow_of_le h_p_gt_1 (by omega)
        _ = 1 := by simp
        _ > 0 := by positivity

    have : p^(k - 1) * (p - 1) > 0 := Nat.mul_pos h_p_pow (by omega)

    -- n is positive
    have: n>0 := by
      by_contra h_contra
      push_neg at h_contra
      have: n = 0 := by omega
      rcases h2 with ⟨c, hc⟩
      have : p^(k - 1) * (p - 1) = 0 := by
        calc
          _ = n * c := by rw [hc]
          _ = 0 := by simp [this]
      linarith

    -- case1: k = 1, case2: k > 1
    by_cases hk_eq_1: k = 1
    . -- case k = 1
      have : p-1 ≤ n := by exact Nat.le_of_dvd (by omega) h1
      have : n ≤ p-1 := by
        calc
          _ ≤  p ^ (k - 1) * (p - 1) := by exact Nat.le_of_dvd (by omega) (h2)
          _ = p-1 := by simp [hk_eq_1]
      have: n = p-1 := by omega
      use 0
      constructor
      . -- show 0 ≤ k -1
        simp [hk_eq_1]
      . -- show n = p - 1
        norm_num; exact this
    .
      -- write n = m * (p - 1)
      push_neg at hk_eq_1
      have hk_gt_1: k ≥ 2 := by omega
      set m := n / (p - 1) with hm
      have hn : n = m * (p - 1) := by exact Eq.symm (Nat.div_mul_cancel h1)
      -- from n ∣ p^(k-1)*(p-1) we get m ∣ p^(k-1)

      have h_mul_dvd: m * (p - 1) ∣ p^(k-1) * (p - 1) := by
        calc
          _ = n := by rw [hn]
          _ ∣ p^(k-1) * (p - 1) := h2

      have h_dvd: m ∣ p^(k-1) := Nat.dvd_of_mul_dvd_mul_right (by omega) h_mul_dvd

      -- use the lemma to get d
      obtain ⟨d, hd_le, hd_eq⟩ := (Nat.dvd_prime_pow hp).mp h_dvd
      use d
      constructor
      . exact hd_le
      . simp [hd_eq, hn]


  -- Case 1: prove that (ZMod (p ^ k))ˣ is cyclic

  have is_cyclic_zmod_prime_pow : IsCyclic (ZMod (p ^ k))ˣ:= by
    -- abbreviations
    set G := (ZMod (p ^ k))ˣ

    -- basic facts
    have h_p_prime : Nat.Prime p := hp.out

    have h_p_ge_3 : p ≥ 3 := by
      have h_ne_two : p ≠ 2 := by
        intro h
        rw [h] at hp1
        have :Even p := (Nat.Prime.even_iff h_p_prime).mpr h
        have : p % 2 = 0 := Nat.even_iff.mp this
        have : p % 2 = 1 := Nat.odd_iff.mp (h ▸ hp1)
        linarith
      have: 1 < p := Nat.Prime.one_lt h_p_prime
      omega

    -- The group of units mod p^k has cardinality p^(k-1) * (p-1)
    have h_card_G: Nat.card G = p^(k-1) * (p-1) := by
      calc
        _ = Fintype.card (ZMod (p ^ k))ˣ := by exact Nat.card_eq_fintype_card
        _ = (p ^ k).totient := ZMod.card_units_eq_totient (p ^ k)
        _ = p ^ (k-1) * (p-1) := by exact Nat.totient_prime_pow (by exact h_p_prime) (by omega)

    -- 1. build the p-Sylow subgroup U = ⟨1 + p⟩
    have h_p_sub_1: 1 + p - 1 = p := by omega
    have h_p_dvd: p ∣ 1 + p - 1:= by rw [h_p_sub_1]
    have h_pow: p ^ (k - 1) ≥ 1 := by
      calc
        _ ≥ p ^ 0 := Nat.pow_le_pow_right (by positivity) (by positivity)
        _ = 1 := by norm_num
    have h_pow_ne_0: p ^ (k - 1) ≠ 0 := by omega

    have h_p_not_dvd: ¬p ∣ 1 + p := by
      intro h
      have : p ∣ 1 := by exact Nat.dvd_add_self_right.mp h
      have: p ≤ 1 := by exact Nat.le_of_dvd (by positivity) this
      linarith

    have: (1 + p) ^ (p ^ (k - 1)) - 1 > 0 := by
      calc
        _ ≥ (1 + p) ^ 1 - 1 := by gcongr; omega
        _ = p := by simp
        _ > 0 := by positivity

    have h_1:  (1 + p : ZMod (p ^ k)) ^ (p ^ (k - 1)) = 1 := by
      -- use the LTE lemma to show that the order of 1 + p is p^(k-1)
      have h_lte: multiplicity p ((1 + p) ^ (p ^ (k - 1)) - 1) = k := by
        calc
          _ = padicValNat p ((1 + p) ^ (p ^ (k - 1)) - 1) := by rw [padicValNat_def (by positivity)]
          _ = padicValNat p ((1 + p) ^ (p ^ (k - 1)) - 1 ^ (p ^ (k - 1))) := by ring_nf
          _ = padicValNat p (1 + p - 1) + padicValNat p (p ^ (k - 1)):= padicValNat.pow_sub_pow (by exact
            hp1: Odd p) (by omega: 1 < 1 + p) h_p_dvd h_p_not_dvd h_pow_ne_0
          _ = 1 + (k - 1) := by
            rw [h_p_sub_1, padicValNat.prime_pow]
            simp [h_p_dvd]
          _ = k := by omega

      -- convert padicValNat to multiplicity
      have h_p_pow_dvd: p^k ∣ (1 + p) ^ (p ^ (k - 1)) - 1 := pow_dvd_of_le_multiplicity (by omega: k ≤ multiplicity p ((1 + p) ^ (p ^ (k - 1)) - 1))

      -- cast h_p_pow_dvd to ZMod
      have h_zmod := (ZMod.natCast_zmod_eq_zero_iff_dvd ((1 + p) ^ (p ^ (k - 1)) - 1) (p^k)).mpr h_p_pow_dvd

      rw [Nat.cast_sub, Nat.cast_pow, Nat.cast_add] at h_zmod

      . norm_num at h_zmod
        exact sub_eq_zero.mp h_zmod
      . omega

    have h_1':  ((1 + p: ℕ): ZMod (p ^ k)) ^ (p ^ (k - 1)) = 1:= by simp [h_1]

    set r := orderOf ((1 + p: ℕ): ZMod (p ^ k))

    have h_2: r = p ^ (k - 1) := by

      -- divide into two cases: k = 1 and k > 1
      by_cases hk_eq_1: k = 1
      . -- case k = 1
        simp [hk_eq_1, ZMod.natCast_zmod_eq_zero_iff_dvd, r]
      . -- case k > 1
        have hk_gt_1: k > 1 := by omega
        have hk_ge_2: k ≥ 2 := by omega
        have hk_sub_2: k - 2 ≥ 0 := by omega

        have : p ^ (k - 2) ≥ 1 := by
          calc
            _ ≥ p ^ 0 := by gcongr; omega
            _ = 1 := by simp

        -- show that (1 + p) ^ (p ^ (k - 2)) - 1 is positive
        have h_pos: (1 + p) ^ (p ^ (k - 2)) - 1 > 0 := by
          calc
            _ ≥ (1 + p) ^ 1 - 1 := by gcongr; omega
            _ = p := by simp
            _ > 0 := by positivity

        -- use the LTE lemma to show that the order of 1 + p is p^(k-2)
        have h_lte': multiplicity p ((1 + p) ^ (p ^ (k - 2)) - 1) = k - 1 := by
          calc
            _ = padicValNat p ((1 + p) ^ (p ^ (k - 2)) - 1) := by rw [padicValNat_def (by positivity)]
            _ = padicValNat p ((1 + p) ^ (p ^ (k - 2)) - 1 ^ (p ^ (k - 2))) := by ring_nf
            _ = padicValNat p (1 + p - 1) + padicValNat p (p ^ (k - 2)):= padicValNat.pow_sub_pow (by exact
              hp1: Odd p) (by omega: 1 < 1 + p) h_p_dvd h_p_not_dvd (by omega: p ^ (k - 2) ≠ 0)
            _ = 1 + (k - 2) := by
              rw [h_p_sub_1, padicValNat.prime_pow]
              simp [h_p_dvd]
            _ = k - 1 := by omega

        have h_finite : FiniteMultiplicity p ((1 + p) ^ (p ^ (k - 2)) - 1) := by
          refine Nat.finiteMultiplicity_iff.mpr ?_
          constructor
          . omega
          . exact h_pos

        have h_p_pow_dvd': ¬ p^k ∣ (1 + p) ^ (p ^ (k - 2)) - 1 := FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt h_finite (by omega: multiplicity p ((1 + p) ^ (p ^ (k - 2)) - 1) < k)

        have h_r_dvd: r ∣ p ^ (k - 1) := orderOf_dvd_of_pow_eq_one h_1'
        have h_r_le : r ≤ p ^ (k - 1) := Nat.le_of_dvd (by omega) h_r_dvd

        obtain ⟨m, hm_le, hr_eq⟩ := (Nat.dvd_prime_pow h_p_prime).mp h_r_dvd

        have: r = p ^ (k - 1) := by
          by_contra h_r_ne
          have h_r_lt : p ^ m < p ^ (k - 1) := by omega
          have : m < k-1 := (pow_lt_pow_iff_right₀ (by omega: 1 < p)).mp h_r_lt
          have : m ≤ k-2 := by omega
          have : p^m ∣ p ^ (k - 2):= Nat.pow_dvd_pow p this
          have : r ∣ p ^ (k - 2):= by simp [hr_eq, this]
          have h_1_plus_p_pow: ((1 + p: ℕ): ZMod (p ^ k))^(p ^ (k - 2)) = 1 := by exact orderOf_dvd_iff_pow_eq_one.mp this
          rw [←Nat.cast_pow] at h_1_plus_p_pow
          nth_rw 2 [←Nat.cast_one] at h_1_plus_p_pow
          have h_mod_eq: (1 + p) ^ p ^ (k - 2) ≡ 1 [MOD p ^ k] := (ZMod.eq_iff_modEq_nat (p ^ k)).mp h_1_plus_p_pow
          have h_p_pow_not_dvd':= (Nat.modEq_iff_dvd' (by omega)).mp h_mod_eq.symm
          exact h_p_pow_dvd' h_p_pow_not_dvd'

        exact this

    -- show that there exists an element of order p - 1 in (ZMod (p ^ k))ˣ
    have exists_lifted_order_of_pow :
      ∃ x : (ZMod (p ^ k))ˣ, orderOf x = p - 1 := by

      have h_p_prime : Nat.Prime p := hp.out
      have: p≥ 2 := Nat.Prime.two_le h_p_prime
      have: p^k ≥ 2 := by
        calc
          _ ≥ p ^ 1 := by exact Nat.pow_le_pow_of_le this hk
          _ = p := by simp
          _ ≥ 2 := by omega

      -- show that p divides p^k
      have h_p_dvd: p ∣ p ^ k := by
        refine Dvd.dvd.pow ?_ ?_
        . exact Nat.dvd_refl p
        . omega

      -- Define the mod p reduction homomorphism ψ : (ZMod (p^k))ˣ →* (ZMod p)ˣ
      let ψ : (ZMod (p ^ k))ˣ →* (ZMod p)ˣ :=
        Units.map (ZMod.castHom h_p_dvd (ZMod p))

      -- surjectivity of ψ
      have : NeZero (p ^ k) := { out := by positivity }

      have h_surj : Function.Surjective ψ := ZMod.unitsMap_surjective h_p_dvd
      -- pick a generator y of (ZMod p)ˣ of order p-1

      have h_cyclic : IsCyclic (ZMod p)ˣ := instIsCyclicUnitsOfFinite (R := ZMod p)

      -- The group of units mod p has cardinality p - 1
      have h_card : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p

      -- obtain a generator y of (ZMod p)ˣ
      obtain ⟨y, hy⟩ := h_cyclic.exists_generator

      -- y has order p-1
      have h_order_y: orderOf y = p - 1 := by
        calc
          _ = Nat.card (ZMod p)ˣ := orderOf_eq_card_of_forall_mem_zpowers hy
          _ = p - 1 := by simp [h_card]

      -- lift y to x in source
      obtain ⟨x₀, hx₀⟩ := h_surj y

      -- use orderOf_map_dvd to conclude

      have h_order_x₀: p - 1 ∣ orderOf x₀ := by
        calc
          _ = orderOf (ψ x₀) := by simp [h_order_y, hx₀]
          _ ∣ orderOf x₀ := orderOf_map_dvd ψ x₀


      have h_order_x₀_dvd: orderOf x₀ ∣ p^(k - 1) * (p - 1) := by
        calc
          _ ∣ Nat.card G := orderOf_dvd_natCard x₀
          _ = p^(k-1) * (p-1) := by rw [h_card_G]

      obtain ⟨j, hj, h_order_x₀_eq⟩ := exists_pow_mul p k (orderOf x₀) h_p_prime hk h_order_x₀ h_order_x₀_dvd


      by_cases hj_eq_0: j = 0
      . -- case j = 0
        use x₀
        simp [h_order_x₀_eq, hj_eq_0]

      . -- case j > 0
        have: j ≥ 1 := by omega
        have: j ≤ k - 1 := by omega

        set x := x₀^(p^j) with hx

        use x

        -- show that x^(p-1) = 1
        have h_x_pow_p_minus_1 : x^(p-1) = 1 := by
          calc
            _ = (x₀^(p^j))^(p-1) := by simp [hx]
            _ = x₀^(p^j * (p-1)) := by rw [pow_mul]
            _ = x₀^orderOf x₀ := by rw [h_order_x₀_eq]
            _ = 1 := pow_orderOf_eq_one x₀

        have : orderOf x > 0:= by exact orderOf_pos x
        have h_order_x_dvd_p_minus_1: orderOf x ∣ p - 1 := by exact orderOf_dvd_of_pow_eq_one h_x_pow_p_minus_1

        -- use Fermat's little theorem to show that y ^ (p ^ j) = y
        have h_y_pow_p_j: y ^ (p ^ j) = y:= by
          apply Units.ext
          exact ZMod.pow_card_pow (y : ZMod p)

        -- show that ψ(x) = y
        have h_ψ_x_eq_y: ψ x = y := by
          calc
            _ = ψ (x₀^(p^j)) := by simp [hx]
            _ = ψ (x₀)^(p^j) := MonoidHom.map_pow ψ x₀ (p ^ j)
            _ = y^(p^j) := by simp [hx₀]
            _ = y := h_y_pow_p_j

        -- show that the order of x is p - 1
        have h_order_x₀: p - 1 ∣ orderOf x := by
          calc
            _ = orderOf (ψ x₀) := by simp [h_order_y, hx₀]
            _ = orderOf (y) := by simp [hx₀]
            _ = orderOf (ψ x) := by simp [h_ψ_x_eq_y]
            _ ∣ orderOf x := orderOf_map_dvd ψ x

        -- get both upper and lower bounds on the order of x,
        -- which forces the `orderOf x` to be p - 1
        have: p - 1 ≤ orderOf x := Nat.le_of_dvd (by omega) h_order_x₀
        have: orderOf x ≤ p - 1 := Nat.le_of_dvd (by omega) h_order_x_dvd_p_minus_1
        omega

    obtain ⟨g, hg⟩ := exists_lifted_order_of_pow

    -- show that p^(k-1) and p-1 are coprime
    have h_order_coprime: (p^(k-1)).Coprime (p-1) := by
      have h_coprime: (p-1).Coprime p := (Nat.coprime_of_lt_prime (by omega) (by omega) h_p_prime).symm
      by_cases h_p_eq_2: k=1
      . -- case k = 1
        simp [h_p_eq_2]

      . -- case k > 1
        push_neg at h_p_eq_2
        exact ((Nat.coprime_pow_right_iff (by omega) (p-1) p).mpr h_coprime).symm

    -- show that the inverse of 1 + p is (1 + p) ^ (p ^ (k - 1) - 1)
    have h_val_inv: (1 + p : ZMod (p ^ k)) * (1 + p : ZMod (p ^ k)) ^ (p ^ (k - 1) - 1) = 1 := by
      nth_rw 1 [show (1 + p : ZMod (p ^ k)) = (1 + p) ^ 1 by simp]
      have : p ^ (k - 1) - 1 ≥ 0:= by omega
      calc
        _ = (1 + p : ZMod (p ^ k)) ^ (1 + (p ^ (k - 1) - 1)) := by
          rw [<-pow_add]
        _ = (1 + p : ZMod (p ^ k)) ^ (p ^ (k - 1)) := by
          congr

          omega
        _ = 1 := by simp [h_1]

    have h_inv_val: (1 + p : ZMod (p ^ k)) ^ (p ^ (k - 1) - 1) * (1 + p : ZMod (p ^ k)) = 1 := by rw [mul_comm, h_val_inv]

    -- construct u = 1 + p as an element in G=(ZMod (p ^ k))ˣ
    let u : G := Units.mk (1 + p : ZMod (p ^ k)) ((1 + p : ZMod (p ^ k)) ^ (p ^ (k - 1) - 1)) h_val_inv h_inv_val

    -- show that the order of u is p^(k-1)
    have h_order_u: orderOf u = p ^ (k - 1) := by
      calc
        _ = orderOf (u : ZMod (p ^ k)) := by rw[orderOf_units]
        _ = orderOf (1 + p : ZMod (p ^ k)) := by rfl
        _ = r := by simp [r]
        _ = p ^ (k - 1) := by rw [h_2]

    -- show that u and g commute
    have h_commute: Commute u g := by exact Commute.all u g

    have hco: (orderOf u).Coprime (orderOf g) := by
      rw [h_order_u, hg]
      exact h_order_coprime

    -- show that the order of u * g is the cardinality of G
    have h_order_ug: orderOf (u * g) = Nat.card G := by
      calc
        _ = orderOf u * orderOf g := Commute.orderOf_mul_eq_mul_orderOf_of_coprime h_commute hco
        _ = p ^ (k - 1) * (p - 1) := by simp [h_order_u, hg]
        _ = Nat.card G := by rw [h_card_G]


    exact isCyclic_of_orderOf_eq_card (u * g) h_order_ug


  -- Case 2: prove that (ZMod (2 * p ^ k))ˣ is cyclic
  have is_cyclic_zmod_2_mul_prime_pow : IsCyclic (ZMod (2 * p ^ k))ˣ := by

    have h_p_prime : Nat.Prime p := hp.out

    have h_p_ge_3 : p ≥ 3 := by
      have h_ne_two : p ≠ 2 := by
        intro h
        rw [h] at hp1
        have :Even p := (Nat.Prime.even_iff h_p_prime).mpr h
        have : p % 2 = 0 := Nat.even_iff.mp this
        have : p % 2 = 1 := Nat.odd_iff.mp (h ▸ hp1)
        linarith
      have: 1 < p := Nat.Prime.one_lt h_p_prime
      omega

    have h_coprime: Nat.Coprime 2 (p ^ k) := by
      refine Nat.Prime.coprime_pow_of_not_dvd ?_ ?_
      . exact h_p_prime
      . refine Nat.not_dvd_of_pos_of_lt (by omega) (by omega)


    -- We can prove this by creating a multiplicative equivalence (≃*)
    -- which is stronger and automatically implies a plain equivalence (≃).
    -- The proof is a composition (trans) of two steps.
    have e: (ZMod (2 * (p ^ k)))ˣ ≃* (ZMod 2)ˣ × (ZMod (p ^ k))ˣ :=
      -- Step 1: Use the Chinese Remainder Thm to map units to units of the product ring.
      (Units.mapEquiv (ZMod.chineseRemainder h_coprime).toMulEquiv)
      -- Step 2: Swap the units of a product with the product of the units.
      |>.trans (MulEquiv.prodUnits)


    -- The group of units mod 2 has cardinality 1
    have h_card : Fintype.card (ZMod 2)ˣ = 1 := by
      calc
        _ = Nat.totient 2 := by rw [ZMod.card_units_eq_totient 2]
        _ = 2 - 1 := by exact Nat.totient_prime (by decide: Nat.Prime 2)
        _ = 1 := by norm_num

    -- The group of units mod 2 is trivial
    have h_unique_prod: Unique (ZMod 2)ˣ := by
      exact Unique.mk' (ZMod 2)ˣ

    -- product with the trivial group is isomorphic to the original group
    have h_isom: (ZMod 2)ˣ × (ZMod (p ^ k))ˣ ≃* (ZMod (p ^ k))ˣ := MulEquiv.uniqueProd

    -- compose the two isomorphisms to get an isomorphism from (ZMod (2 * p ^ k))ˣ to (ZMod (p ^ k))ˣ
    have h_comp: (ZMod (2 * (p ^ k)))ˣ ≃* (ZMod (p ^ k))ˣ := by
      exact e.trans h_isom

    -- the inverse of the isomorphism `h_comp` is an isomorphism from (ZMod (p ^ k))ˣ to (ZMod (2 * (p ^ k)))ˣ
    have h_comp_inv: (ZMod (p ^ k))ˣ ≃* (ZMod (2 * (p ^ k)))ˣ := h_comp.symm

    -- the inverse of the isomorphism `h_comp` is surjective
    exact isCyclic_of_surjective h_comp_inv h_comp_inv.surjective


  -- conclude that both (ZMod (p ^ k))ˣ and (ZMod (2 * p ^ k))ˣ are cyclic
  constructor
  . exact is_cyclic_zmod_prime_pow
  . exact is_cyclic_zmod_2_mul_prime_pow
