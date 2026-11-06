import Mathlib

open Polynomial

/- For the equation $x^{2}-a x+b=0$, the two roots are $\alpha, \beta$, and for $x^{2}-b x+c=0$, the two roots are $\gamma, \delta$ ($\alpha, \beta, \gamma, \delta$ are all distinct). Let $M=\{\alpha, \beta, \gamma, \delta\}, u, v \in M(u \neq v), S=\{x \mid x=u+v\}, P=\{x \mid x=u, v\}$. Also, $S=\{5, 7, 8, 9, 10, 12\}, P=\{6, 10, 14, 15, 21, 35\}$, find $a, b, c$. -/
theorem algebra_251283 (a b c α β γ δ : ℝ) (p1 p2 : ℝ[X])
    (h1 : [α, β, γ, δ].Nodup)
    (M S P: Finset ℝ)
    (hM : M = {α, β, γ, δ})
    (hp1 : p1 = X ^ 2 - C a * X + C b)
    (hp1r : p1.roots = {α, β})
    (hp2 : p2 = X ^ 2 - C b * X + C c)
    (hp2r : p2.roots = {γ, δ})
    (hS : ∀ x, (∃ u v, u ∈ M ∧ v ∈ M ∧ u ≠ v ∧ u + v = x) ↔ x ∈ S)
    (hP : ∀ x, (∃ u v, u ∈ M ∧ v ∈ M ∧ u ≠ v ∧ u * v = x) ↔ x ∈ P)
    (hS_eq : S = {5, 7, 8, 9, 10, 12})
    (hP_eq : P = {6, 10, 14, 15, 21, 35}) :
    a = 7 ∧ b = 10 ∧ c = 21 := by
    -- normalize polynomials
    have p1_eq : p1 = X ^ 2 + C (-a) * X + C b := by
      simp only [hp1, one_mul, map_neg, neg_mul, ←sub_eq_add_neg]

    have p2_eq : p2 = X ^ 2 + C (-b) * X + C c := by
      simp only [hp2, one_mul, map_neg, neg_mul, ←sub_eq_add_neg]

    -- we have vietas formula for monic quadratic polynomials
    have vieta : ∀ {a b c d : ℝ}, (X ^ 2 + C a * X + C b).roots = {c, d} → (b = c * d ∧ a = -(c + d)) := by
      intro a b c d h
      -- let p be the polynomial x ^ 2 + a * x + b
      let p := (1 * X ^ 2 + C a * X + C b)

      -- and the roots be c and d
      convert_to p.roots = {c, d} at h
      · unfold p
        rw [one_mul]

      -- then p has degree 2
      have degree : p.natDegree = 2 := Polynomial.natDegree_quadratic (by norm_num)

      -- and as many roots as degree
      have roots_card : p.roots.card = p.natDegree := by
        rw [degree, h]
        norm_num

      -- 0th coefficient of p is b, 1st coefficient of p is a
      have coeff_0 : p.coeff 0 = b := by unfold p; norm_num
      have coeff_1 : p.coeff 1 = a := by unfold p; norm_num

      -- p has a leading coefficient of 1
      have leading : p.leadingCoeff = 1 := Polynomial.leadingCoeff_quadratic (by norm_num)

      -- 0 and 1 are less than or equal to the degree, so it makes sense to talk about the 0th and 1st coefficient
      have zero_le : 0 ≤ p.natDegree := by linarith
      have one_le : 1 ≤ p.natDegree := by linarith

      constructor
      -- apply the general form of Vieta's formula to the 0th coefficient of p
      · have vieta := Polynomial.coeff_eq_esymm_roots_of_card roots_card zero_le

        -- simplifying we get b = c * d
        simpa only [coeff_0, leading, degree, tsub_zero, even_two, Even.neg_pow, one_pow, mul_one,
          Multiset.esymm, h, Multiset.insert_eq_cons, Multiset.powersetCard_cons, Nat.reduceAdd,
          Multiset.card_singleton, Nat.one_lt_ofNat, Multiset.powersetCard_eq_empty,
          Multiset.powersetCard_one, Multiset.map_singleton, zero_add, Multiset.prod_cons,
          Multiset.prod_singleton, Multiset.sum_singleton, one_mul] using vieta
      -- apply the general form of Vieta's formula to the 1st coefficient of p
      · have vieta := Polynomial.coeff_eq_esymm_roots_of_card roots_card one_le
        -- simplifying we get a = -(c + d)
        simp only [coeff_1, leading, degree, Nat.add_one_sub_one, pow_one, mul_neg, mul_one,
          Multiset.esymm, h, Multiset.insert_eq_cons, Multiset.powersetCard_cons, zero_add,
          Multiset.powersetCard_one, Multiset.map_singleton, Multiset.powersetCard_zero_left,
          Multiset.cons_zero, Multiset.singleton_add, Multiset.map_cons, Multiset.prod_singleton,
          Multiset.sum_cons, Multiset.sum_singleton, neg_mul, one_mul, neg_add_rev] at vieta
        linarith

    -- we apply Vieta's formula to the quadratic polynomial x ^ 2 - a * x + b with roots {α, β}
    -- we get b = α * β and a = α + β
    have ⟨p1_vieta_1, p1_vieta_2⟩ : b = α * β ∧ a = α + β := by
      rw [p1_eq] at hp1r
      have ⟨v1, v2⟩ := vieta hp1r
      exact ⟨v1, neg_inj.mp v2⟩

    -- we apply Vieta's formula to the quadratic polynomial x ^ 2 - b * x + c with roots {γ, δ}
    -- we get c = γ * δ and b = γ + δ
    have ⟨p2_vieta_1, p2_vieta_2⟩ : c = γ * δ ∧ b = γ + δ := by
      rw [p2_eq] at hp2r
      have ⟨v1, v2⟩ := vieta hp2r
      exact ⟨v1, neg_inj.mp v2⟩

    -- α, β, γ, δ are all part of M
    have ⟨set_list_α, set_list_β, set_list_γ, set_list_δ⟩ : α ∈ M ∧ β ∈ M
      ∧ γ ∈ M ∧ δ ∈ M := by
      simp only [hM, Finset.mem_insert, Finset.mem_singleton, true_or, or_true, and_self]

    -- using Vieta's formula, we see that b is part of S
    have b_mem_S : b ∈ S := by
      apply (hS b).mp
      exists γ, δ

      have γ_ne_δ : γ ≠ δ := by
        convert_to [α, β, γ, δ][2] ≠ [α, β, γ, δ][3]
        refine h1.getElem_inj_iff.ne.mpr ?_
        decide

      -- because b = γ + δ
      exact ⟨set_list_γ, set_list_δ, γ_ne_δ, p2_vieta_2.symm⟩

    -- we also see that b is part of P
    have b_mem_P : b ∈ P := by
      apply (hP b).mp
      exists α, β

      have α_ne_β : α ≠ β := by
        convert_to [α, β, γ, δ][0] ≠ [α, β, γ, δ][1]
        refine h1.getElem_inj_iff.ne.mpr ?_
        decide

      -- because b = α * β
      exact ⟨set_list_α, set_list_β, α_ne_β, p1_vieta_1.symm⟩

    -- The only common element between S and P is 10
    have common_11 : S ∩ P = {10} := by
      -- every element of S is a natural number
      have S_eq_map : ({5, 7, 8, 9, 10, 12} : Finset ℝ)
        = Finset.map Nat.castEmbedding {5, 7, 8, 9, 10, 12} := by norm_num
      -- every element of P is a natural number
      have P_eq_map : ({6, 10, 14, 15, 21, 35} : Finset ℝ)
        = Finset.map Nat.castEmbedding {6, 10, 14, 15, 21, 35} := by norm_num

      -- the left hand side is also a natural number
      have rhs : ({10} : Finset ℝ) = Finset.map Nat.castEmbedding {10} := by norm_num

      -- then we have an equality of finite sets of natual numbers
      rw [hS_eq, hP_eq, S_eq_map, P_eq_map, ←Finset.map_inter, rhs, Finset.map_inj]

      -- check and see that the LHS is equal to the RHS
      decide

    -- b is a member of both S and P
    have b_mem_both : b ∈ S ∩ P := Finset.mem_inter_of_mem b_mem_S b_mem_P

    -- so b is 10
    have b_eq : b = 10 := Finset.mem_singleton.mp (common_11 ▸ b_mem_both)
    subst b_eq

    -- we have that the sum of all members of S is 51
    have S_sum : ∑ i ∈ S, i = 51 := by
      rw [hS_eq]
      norm_num

    -- let f be an ordering of α, β, γ, δ
    let f : Fin 4 → ℝ := fun i => [α, β, γ, δ][i]

    -- the ordering as a finset is equal to M
    have list_tofinset : [α, β, γ, δ].toFinset = M := by rw [hM]; norm_num

    -- if a variable is part of M, then it has a position in the ordering
    have mem_list_of_mem_set : ∀ {x}, x ∈ M → ∃ i, f i = x := by
      intro x xh
      rw [←list_tofinset, List.mem_toFinset] at xh
      obtain ⟨i, ih, ihh⟩ :=  List.exists_mem_iff_getElem.mp ⟨x, xh, rfl⟩
      exact ⟨⟨i, ih⟩, ihh.symm⟩

    -- let T be the tuples (u, v), where 0 ≤ u, v < 4 and u < v, i.e.
    -- T = (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)
    let T : Finset (Fin 4 × Fin 4) := {⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨2, 3⟩}
    have univ_filter_eq : Finset.univ.filter (fun x => x.1 < x.2) = T := by decide

    -- Both S and P can be represented as the image of a set of six pairs
    -- only difference is that S uses +, and P uses *
    have as_finite : ∀ {F : Finset ℝ} {op : ℝ → ℝ → ℝ} [hop : Std.Commutative op],
      (∀ x, (∃ u v, u ∈ M ∧ v ∈ M ∧ u ≠ v ∧ op u v = x) ↔ x ∈ F) → F = T.image (fun (u, v) => op (f u) (f v))
      := by
        intro F op hop hF
        rw [←univ_filter_eq]
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
        constructor
        · intro aa
          obtain ⟨a1, b1, cc, dd, ee, ff⟩ := (hF x).mpr aa
          obtain ⟨a, ah⟩ := mem_list_of_mem_set cc
          obtain ⟨b, bh⟩ := mem_list_of_mem_set dd
          rcases lt_trichotomy a b with h1 | h2 | h3
          · exact ⟨a, b, h1, ah ▸ bh ▸ ff⟩
          · rw [h2] at ah
            rw [ah] at bh
            contradiction
          · refine ⟨b, a, h3, ?_⟩
            rw [ah, bh, hop.comm b1 a1]
            exact ff
        · intro ⟨a, b, cc, dd⟩
          apply (hF x).mp
          exists f a, f b
          rw [←list_tofinset, List.mem_toFinset, List.mem_toFinset]
          unfold f
          refine ⟨?_, ?_, ?_, dd⟩
          · norm_num
          · norm_num
          · have a_ne_b : a.1 ≠ b.1 := Nat.ne_of_lt cc
            exact ((List.Nodup.getElem_inj_iff h1).ne).mpr a_ne_b

    have S_finite := as_finite hS
    have P_finite := as_finite hP

    -- both S and P have six elements
    have S_card : S.card = 6 := by rw [hS_eq]; norm_num
    have P_card : P.card = 6 := by rw [hP_eq]; norm_num

    -- there are six tuples
    have doubles_card : 6 = T.card := by decide

    -- so the mapping from tuples is injective
    have eq := S_finite ▸ (S_card.trans doubles_card)

    have injon := Finset.card_image_iff.mp eq

    -- recall that f maps from Fin 4 to α, β, γ, δ
    have f_0_eq : f 0 = α := rfl
    have f_1_eq : f 1 = β := rfl
    have f_2_eq : f 2 = γ := rfl
    have f_3_eq : f 3 = δ := rfl

    -- then we have that the sum of S is equal to 3 * (α + β + γ + δ)
    have S_eq : ∑ i ∈ S, i = 3 * (α + β + γ + δ) := by
      rw [S_finite, Finset.sum_image @injon]
      unfold T
      simp only [Fin.isValue, Finset.mem_insert, Prod.mk.injEq, Fin.reduceEq, and_false,
        zero_ne_one, and_self, Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
        and_true, Finset.sum_singleton]

      rw [f_0_eq, f_1_eq, f_2_eq, f_3_eq]
      ring

    rw [S_sum] at S_eq

    -- so we have that 7 = α + β
    replace S_eq : 7 = α + β := by linarith

    -- so a = 7
    have a_eq : a = 7 := by linarith
    subst a_eq

    -- the product of all values in P is 210 ^ 3
    have P_prod : ∏ i ∈ P, i = 210 ^ 3 := by rw [hP_eq]; norm_num

    -- the mapping from tuples is injective in this case too
    have eq := P_finite ▸ (P_card.trans doubles_card)
    have injon := Finset.card_image_iff.mp eq

    -- the product of all values in P (αβγδ) ^ 3
    have P_eq : ∏ i ∈ P, i = (α * β * γ * δ) ^ 3 := by
      rw [P_finite, Finset.prod_image @injon]
      unfold T
      simp only [Fin.isValue, Finset.mem_insert, Prod.mk.injEq, Fin.reduceEq, and_false,
        zero_ne_one, and_self, Finset.mem_singleton, or_self, not_false_eq_true, Finset.prod_insert,
        and_true, Finset.prod_singleton]
      rw [f_0_eq, f_1_eq, f_2_eq, f_3_eq]
      ring

    -- so (α * β * γ * δ) ^ 3 = 210 ^ 3
    rw [P_prod] at P_eq

    -- then (α * β * γ * δ) = 210
    have mul_eq : 210 = α * β * γ * δ := by
      have three_ne_zero : 3 ≠ 0 := by norm_num
      have not_even : ¬Even 3 := by decide
      simpa only [not_even, and_false, or_false] using (pow_eq_pow_iff_of_ne_zero three_ne_zero).mp P_eq

    -- γ * δ = 21
    have mul_eq : γ * δ = 21 := by
      rw [←p1_vieta_1] at mul_eq
      linarith

    -- c = 21
    have c_eq : c = 21 := by linarith

    -- so a = 7, b = 10, c = 21
    exact ⟨rfl, rfl, c_eq⟩