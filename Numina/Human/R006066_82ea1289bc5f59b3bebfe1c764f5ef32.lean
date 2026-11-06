import Mathlib

open Finset Fin

/- In a chess-playing club, some of the players take lessons from other players.
It is possible (but not necessary) for two players both to take lessons from each other.
It so happens that for any three distinct members of the club, $A, B$, and $C$,
exactly one of the following three statements is true: $A$ takes lessons from $B$;
$B$ takes lessons from $C$; $C$ takes lessons from $A$. What is the largest number of
players there can be? -/
theorem number_theory_611378 :
    IsGreatest {n |
      ∃ r : Finset (Fin n × Fin n),
      (∀ A, (A, A) ∉ r) ∧
      (∀ A B C : Fin n, A ≠ B → B ≠ C → C ≠ A →
        (r ∩ {(A, B), (B, C), (C, A)}).card = 1)} 4 := by
  refine ⟨?_, fun n hn => ?_⟩
  · -- One direction: There exists a learning relationship with 4 players.
    -- Player 0 and 1 learn from each other, and player 2 and 3 learn from each other.
    use {(0, 1), (1, 0), (2, 3), (3, 2)}
    refine (?_ : ?result)
    simpa using show (?result : Bool) from rfl
  · -- The other direction: No learning relationship exists with 5 players.
    by_contra h
    -- Simplify `¬n ≤ 4` to `4 < n`, which by definition is the same as `5 ≤ n`.
    -- In Lean, for natural numbers `a, b`, `a < b` is defined as `a + 1 ≤ b`.
    simp only [not_le] at h
    rcases hn with ⟨r, hn₁, hn₂⟩
    -- It suffices to prove the non-existence for exactly 5 players.
    wlog hn : n = 5
    · -- If there are more than `5` players, consider the learning relationships
      -- among players `0, 1, 2, 3, 4` to derive a contradiction.
      let f := Prod.map (castLE h) (castLE h)
      have hf : f.Injective := by simp [Function.Injective, f]
      let S := r.preimage f (Set.injOn_of_injective hf)
      refine this 5 (by simp) S ?_ ?_ rfl
      · -- For the learning relationships among the first 5 players, no one learns from themselves.
        simp [S, hn₁, f]
      · -- For the learning relationships among the first 5 players,
        -- exactly one of `A` learns from `B`, `B` learns from `C`,
        -- or `C` learns from `A` holds. This can be intuitively derived from `hn₂`.
        intro A B C hAB hBC hCA
        convert hn₂
          (A.castLE h) (B.castLE h) (C.castLE h)
          (castLE_inj.not.mpr hAB) (castLE_inj.not.mpr hBC) (castLE_inj.not.mpr hCA)
          using 1
        -- In formalization, we need to use the property that `f` is injective and
        -- consider the preimage of `r` along `f`.
        transitivity r ∩ {
            (castLE h A, castLE h B),
            (castLE h B, castLE h C),
            (castLE h C, castLE h A)
          } |>.preimage f (Set.injOn_of_injective hf) |>.card
        · -- This step expresses elements like `(A, B)` as preimages of elements
          -- like `(castLE h A, castLE h B)` under `f`.
          simp only [S, preimage_inter, Set.injOn_of_injective, hf]
          congr 2
          apply image_injective hf
          simp [image_preimage, f, filter_true_of_mem]
        · -- The size of the preimage of `S` along the injective function `f`
          -- equals the size of `S` intersected with the image of `f`.
          rw [card_preimage, filter_true_of_mem]
          simp [f, isLt]
          intro a b _ eq
          rcases eq with eq | eq | eq <;> simp [eq]
    · -- Since `n` is exactly `5`, we can use `subst` or `case` to replace all `n` with 5.
      subst hn
      clear h
      -- Define `X` as the set of all `(A, B, C)` where `A, B, C` are all less than 5
      -- (they are player indices) and pairwise distinct.
      let X := (univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter
        fun (A, B, C) => A ≠ B ∧ B ≠ C ∧ C ≠ A
      -- Clearly, `X` has `60` elements.
      have card_S : X.card = 60 := rfl
      -- For any `(A, B, C)` in `X`, there exists an `x ∈ r ∩ {(A, B), (B, C), (C, A)}`.
      -- In fact, this element is unique.
      have X_map_r : ∀ x ∈ X,
          match x with
          | (A, B, C) => ∃ x, x ∈ r ∩ {(A, B), (B, C), (C, A)} := by
        rintro ⟨A, B, C⟩ h
        simp [X] at h
        obtain ⟨a, ha⟩ := card_eq_one.mp (hn₂ A B C h.1 h.2.1 h.2.2)
        simp [ha]
      -- Use the `choose!` tactic to select the choice function `f`.
      choose! f hf using X_map_r
      -- Decompose the size of `S` into the sum of the sizes of its fibers.
      rw [card_eq_sum_card_fiberwise (fun x hs => (mem_inter.mp (hf x hs)).1)] at card_S
      -- Each fiber has size `9`, and the size of `S` is `60`, so `60` must be a multiple of `9`,
      -- which leads to a contradiction.
      have : ∀ a ∈ r, (X.filter (fun x => f x = a)).card = 9 := by
        clear card_S
        rintro ⟨P, Q⟩ hPQ
        -- Without loss of generality, assume this fiber is `{(A, B, C) | f(A, B, C) = (0, 1)}`,
        -- i.e., `P = 0, Q = 1`.
        wlog eq : P = 0 ∧ Q = 1
        · -- We construct a permutation function `φ : Fin 5 → Fin 5` such that `φ 0 = P, φ 1 = Q`.
          -- In other words, we use a bijection to reorder `P` and `Q` to positions `0` and `1`,
          -- respectively.
          have P_ne_Q : P ≠ Q := by intro h; simp [h, hn₁] at hPQ
          let g : Fin 5 → Fin 5 := fun | 0 => P | _ => Q
          obtain ⟨φ₀, hφ₀⟩ := exists_equiv_extend_of_card_eq
            (s := {0, 1}) (t := ⊤) (f := g) (by simp) (by simp) (by simpa using P_ne_Q)
          simp [g] at hφ₀
          let φ := φ₀.trans (Equiv.subtypeUnivEquiv (by simp))
          have hφ : φ 0 = P ∧ φ 1 = Q := by simpa [φ] using hφ₀
          clear_value φ
          clear eq g φ₀ hφ₀
          -- Now we have constructed the required function `φ : Fin 5 ≃ Fin 5` and property
          -- `hφ : φ 0 = P ∧ φ 1 = Q`. We need to reconstruct the set `r` and function `f`
          -- (composed with this permutation `φ`) and prove a series of properties
          -- for the new `r` and `f`.
          convert this
            (r.preimage (Prod.map φ φ) (by simp [Set.injOn_of_injective, Equiv.injective]))
            ?_ ?_
            (fun x => Prod.map φ.symm φ.symm (f (Prod.map φ (Prod.map φ φ) x)))
            ?_ 0 1 ?_ (by simp) using 1
          · -- Prove that the new fiber (constructed using `r` and `f` composed with `φ`)
            -- has the same size as the original fiber.
            simp [Prod.map, Equiv.symm_apply_eq, hφ]
            symm
            apply card_bijective (Prod.map φ (Prod.map φ φ))
            · exact Function.Bijective.prodMap (by simp)
                (Function.Bijective.prodMap (by simp) (by simp))
            · simp [X, Prod.ext_iff]
          · -- For any `A`, `(A, A)` is not in the new set `r`.
            simp [hn₁]
          · -- For the new `r`, prove that exactly one of `(A, B)`, `(B, C)`, or `(C, A)`
            -- must be in `r`.
            intro A B C hAB hBC hCA
            have hf : (Prod.map φ φ).Injective := by simp [Equiv.injective]
            transitivity
              (r ∩ {(φ A, φ B), (φ B, φ C), (φ C, φ A)}).preimage
              (Prod.map φ φ) (Set.injOn_of_injective hf) |>.card
            · simp [preimage_inter, Set.injOn_of_injective, hf]
              congr 2
              apply image_injective hf
              simp [image_preimage, Prod.map]
            · rw [card_preimage, filter_true_of_mem]
              · exact hn₂ (φ A) (φ B) (φ C)
                  (by simpa using hAB) (by simpa using hBC) (by simpa using hCA)
              · simp
          · -- Prove the property of the choice function `f`, i.e., `hf`.
            intro ⟨A, B, C⟩
            simpa [Prod.map, Equiv.symm_apply_eq, Prod.ext_iff, X] using hf ⟨φ A, φ B, φ C⟩
          · -- Prove `(0, 1) ∈ r`.
            simpa [hφ] using hPQ
        · -- Now we prove the conclusion for `P = 0, Q = 1`. We can explicitly give the value of
          -- this fiber as the finite set `S`. First, use `rcases` to replace all occurrences of
          -- `P` with `0` and `Q` with `1` in the goal and all conditions. This is equivalent to
          -- two `subst` steps.
          rcases eq with ⟨⟨_⟩, ⟨_⟩⟩
          let S : Finset (Fin 5 × Fin 5 × Fin 5) := {
            (0, 1, 2), (0, 1, 3), (0, 1, 4),
            (2, 0, 1), (3, 0, 1), (4, 0, 1),
            (1, 2, 0), (1, 3, 0), (1, 4, 0)
          }
          convert show S.card = 9 from rfl using 2
          -- We prove that this fiber is exactly equal to `S`.
          ext ⟨A, B, C⟩
          refine ⟨fun h => ?_, fun h => ?_⟩
          · -- If `(A, B, C)` is an element of this fiber, prove `(A, B, C) ∈ S`.
            -- Since `f(x) = (0, 1) ∈ {(A, B), (B, C), (C, A)}` and `A, B, C` are distinct,
            -- we can proceed by case analysis. For example, if `(0, 1) = (A, B)`, then
            -- `A = 0, B = 1`, and `C` can be `2, 3` or `4`, all of which are in `S`.
            simp at h
            have eq := h.2 ▸ (mem_inter.mp (hf (A, B, C) h.1)).2
            simp at eq
            replace h := h.1
            simp [X] at h
            rcases eq with eq | eq | eq
            -- Discuss three cases, corresponding to `(0, 1)` equaling to
            -- `(A, B)`, `(B, C)`, or `(C, A)`.
            · simp [eq.1.symm, eq.2.symm]
              -- Such goal about `Fin 5` can be solved by `omega`.
              have hC : C = 2 ∨ C = 3 ∨ C = 4 := by omega
              rcases hC with hC | hC | hC <;> (simp only [hC, S]; simp)
            · -- Similar to the first case.
              simp [eq.1.symm, eq.2.symm]
              have hA : A = 2 ∨ A = 3 ∨ A = 4 := by omega
              rcases hA with hA | hA | hA <;> (simp only [hA, S]; simp)
            · simp [eq.1.symm, eq.2.symm]
              have hB : B = 2 ∨ B = 3 ∨ B = 4 := by omega
              rcases hB with hB | hB | hB <;> (simp only [hB, S]; simp)
          · -- Every element in `S` is in the fiber. We need to prove that for any `(A, B, C) ∈ S`,
            -- `(A, B, C) ∈ X` and `f(A, B, C) = (0, 1)`.
            simp only [isValue, mem_filter]
            -- `S` is a subset of `X`; this part is obvious, as it can be verified
            -- by substituting each element in `S`.
            have S_sub_X : S ⊆ X := by
              simp (config := {contextual := true}) [S, X, subset_iff, or_imp]
            refine ⟨S_sub_X h, ?_⟩
            -- Prove `f(A, B, C) = (0, 1)`. First, specialize and simplify some conditions.
            have ne := S_sub_X h
            simp [X] at ne
            specialize hn₂ A B C ne.1 ne.2.1 ne.2.2
            specialize hf (A, B, C) (S_sub_X h)
            simp only at hf
            -- Since the size of `r ∩ {(A, B), (B, C), (C, A)}` is `1`, any two elements in
            -- this set must be equal. By the property of `f`, `f(A, B, C)` is already in
            -- this set, so we only need to prove `(0, 1)` is also in this set.
            refine Subtype.ext_iff.mp
              ((card_le_one_iff_subsingleton_coe.mp (le_of_eq hn₂)).allEq ⟨_, hf⟩ ⟨_, ?_⟩)
            rw [mem_inter]
            refine ⟨hPQ, ?_⟩
            simp only [S] at h
            simp at h
            rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
      -- Use the fact that `9` does not divide `60` to derive a contradiction.
      -- Here, `simp` substitutes the conclusion that each fiber has size `9` and simplifies.
      simp (config := {contextual := true}) [this] at card_S
      rw [mul_comm] at card_S
      -- We obtain `dvd : 9 ∣ 60`, which is absurd, leading to a contradiction.
      have dvd : 9 ∣ 60 := ⟨_, card_S.symm⟩
      absurd dvd
      simpa using show (¬9 ∣ 60 : Bool) from rfl
