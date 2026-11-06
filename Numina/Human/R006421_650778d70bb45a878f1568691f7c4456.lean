import Mathlib

/- We are proving that the (k-1)-th odd multiple of an odd number P is (2k-1)*P.-/
theorem my_favorite_theorem (P k : ℕ) (hP : Odd P) (hk : 0 < k) :
    (Nat.nth { x | Odd x ∧ P ∣ x } (k - 1)) = (2 * k - 1) * P := by
  -- Let p be the predicate "is an odd multiple of P".
  let p : ℕ → Prop := fun x => Odd x ∧ P ∣ x
  -- Let n be the number we claim is the (k-1)-th number satisfying p.
  let n := (2 * k - 1) * P

  -- We need a decidable instance for the predicate p to use `Nat.count`.
  -- This is provable since both `Odd` and divisibility are decidable.
  have : DecidablePred p := by infer_instance

    -- # Step 1: Prove that our target number `n` satisfies the predicate `p`.
  have h_p_n : p n := by
    -- Unfold the definitions of p and n.
    simp only [p, n]
    constructor
    · -- Prove Odd ((2 * k - 1) * P). The product of two odd numbers is odd.
      -- `2 * k - 1` is odd. `P` is odd by hypothesis `hP`.
      apply Odd.mul
      · -- 2 * k - 1 = 2 * (k - 1) + 1, which is odd
        rw [show 2 * k - 1 = 2 * (k - 1) + 1 by omega]
        simp
      · exact hP
    · -- Prove P ∣ (2 * k - 1) * P. This is true by definition.
      exact dvd_mul_left P (2 * k - 1)

  -- # Step 2: Prove that the count of numbers < n satisfying p is exactly k-1.
  -- This is the core of the proof.
  have h_count_n : Nat.count p n = k - 1 := by
    -- By definition, Nat.count p n is the size of the set {m < n | p m}.

    -- We need to find the number of elements in the filtered range.
    -- Let's characterize the elements `m` for which `p m` is true.
    -- `p m` means `m` is an odd multiple of `P`. Since `P` is odd, this means
    -- `m` must be of the form `j * P` where `j` itself is an odd number.
    have h_char : ∀ m, p m ↔ ∃ j, Odd j ∧ m = j * P := by
      intro m
      constructor
      · -- If p m, then m = q*P and m is odd. Since P is odd, q must be odd.
        rintro ⟨h_odd_m, h_dvd_m⟩
        rcases h_dvd_m with ⟨q, rfl⟩
        have h_odd_q : Odd q := by
          rw [← mul_comm] at h_odd_m
          exact Nat.Odd.of_mul_left h_odd_m
        use q
        exact ⟨h_odd_q, mul_comm P q⟩
      · -- If m = j*P with j odd, then m is an odd multiple of P.
        rintro ⟨j, h_odd_j, rfl⟩
        exact ⟨Odd.mul h_odd_j hP, dvd_mul_left P j⟩

    -- We are counting `m` in `Finset.range n` where `p m`.
    -- This is the set of `j * P` where `j` is odd and `j * P < (2 * k - 1) * P`.
    -- Since P > 0, this simplifies to `j < 2 * k - 1`.
    let f : ℕ → ℕ := fun j => j * P
    have hP_pos : 0 < P := Odd.pos hP
    have hf_inj : Function.Injective f := fun j₁ j₂ h => (mul_left_inj' hP_pos.ne').mp h

    -- The set of `m` satisfying `p m` and `m < n` is the image under `f`
    -- of the set of odd numbers `j` less than `2 * k - 1`.
    -- The card of the image of an injective function is the card of the source set.
    rw [Nat.count_eq_card_filter_range]
    rw [show {m ∈ Finset.range n | p m} =
             Finset.map ⟨f, hf_inj⟩ {j ∈ Finset.range (2 * k - 1) | Odd j} by
      ext m
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk, h_char]
      constructor
      · rintro ⟨h_lt_n, ⟨j, h_odd_j, rfl⟩⟩
        use j
        constructor
        · rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨(mul_lt_mul_right hP_pos).mp (by simp only [n] at h_lt_n; exact h_lt_n), h_odd_j⟩
        · rfl
      · rintro ⟨j, hj, rfl⟩
        rw [Finset.mem_filter, Finset.mem_range] at hj
        constructor
        · simp only [f, n]
          exact mul_lt_mul_of_pos_right hj.1 hP_pos
        · use j, hj.2
          ]
    rw [Finset.card_map]
    -- Count odd numbers in range [0, 2*k-1) which equals k-1
    have : (Finset.filter (fun j => Odd j) (Finset.range (2 * k - 1))).card = k - 1 := by
      -- The odd numbers in range [0, 2*k-1) are {1, 3, 5, ..., 2*(k-1)+1}
      -- We establish a bijection with Finset.range (k-1) via i ↦ 2*i + 1
      have h_bij : (Finset.filter (fun j => Odd j) (Finset.range (2 * k - 1))) =
                   (Finset.range (k - 1)).image (fun i => 2 * i + 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · intro ⟨hj_lt, hj_odd⟩
          cases' hj_odd with m hm
          use m
          constructor
          · rw [hm] at hj_lt
            omega
          · exact hm.symm
        · intro ⟨i, hi_lt⟩
          constructor
          · omega
          · rw [← hi_lt.2]
            use i

      rw [h_bij]
      rw [Finset.card_image_of_injective]
      · simp only [Finset.card_range]
      · intro i₁ i₂ h
        have : 2 * i₁ = 2 * i₂ := by linarith
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) this
    rw [this]

  -- # Step 3: Apply the lemma from the list.
  -- `Nat.nth_count (hpn := h_p_n)` gives us `nth p (count p n) = n`.
  -- With our result from Step 2, this becomes `nth p (k - 1) = n`.
  show Nat.nth {x | Odd x ∧ P ∣ x} (k - 1) = (2 * k - 1) * P
  rw [show {x | Odd x ∧ P ∣ x} = p from rfl]
  rw [← h_count_n]
  exact Nat.nth_count h_p_n