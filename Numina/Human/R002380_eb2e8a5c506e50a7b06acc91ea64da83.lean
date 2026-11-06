import Mathlib
open Finset Set Nat Real
noncomputable section

-- Lemma: Prove that a subgroup of order $2$ contains only two elements: $1$ and $a$.
lemma subgroup_two_elements {G : Type*} [Group G] [Fintype G]
  (H : Subgroup G) [Fintype H] (h_card_H : Fintype.card H = 2) (a : G)
  (ha_in_H : a ∈ H) (ha_ne_one : a ≠ 1) : ∀ x ∈ H, x = 1 ∨ x = a := by
  intro x hx
  have h_two_elements : H.carrier = {1, a} := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      simp [hx]
      have h_x_H : x ∈ H := by exact Subgroup.mem_carrier.mp hx
      -- Use contradiction to prove $x = 1$ or $x = a$.
      have h_x_eq : x = 1 ∨ x = a := by
        by_contra h_not
        push_neg at h_not
        have h_x_ne_one : x ≠ 1 := h_not.1
        have h_x_ne_a : x ≠ a := h_not.2
        have h_one_mem : (1 : G) ∈ H := Subgroup.one_mem H
        have h_a_mem : a ∈ H := ha_in_H
        have h_distinct : Fintype.card H ≥ 3 := by
          let S : Set G := {1, a, x}
          have h_S_subset : S ⊆ H.carrier := by
            intro w hw
            rw [Set.mem_insert_iff] at hw
            cases hw with
            | inl h => rw [h]; exact h_one_mem
            | inr h =>
              cases h with
              | inl h => rw [h]; exact h_a_mem
              | inr h => rw [h]; exact h_x_H
          have h_S_ncard : S.ncard = 3 := by
            unfold S
            apply Set.ncard_eq_three.mpr
            exact ⟨1, a, x, ha_ne_one.symm, h_x_ne_one.symm, h_x_ne_a.symm, rfl⟩
          have h_H_finite : H.carrier.Finite := by
            apply Set.toFinite
          -- Prove that the cardinality of $S$$ is at most that of H.carrier.
          have h_ncard_le : S.ncard ≤ H.carrier.ncard := by
            apply Set.ncard_le_ncard
            · exact h_S_subset
            · exact h_H_finite
          have h_H_card_eq : H.carrier.ncard = Fintype.card H := by
            exact Nat.card_eq_fintype_card
          rw [h_H_card_eq, h_S_ncard] at h_ncard_le
          exact h_ncard_le
        linarith [h_card_H]
      exact h_x_eq
    · simp
      intro h_x
      cases h_x with
      | inl h => rw [h]; exact Subgroup.one_mem H
      | inr h => rw [h]; exact ha_in_H
  have h_x_in_set : x ∈ ({1, a} : Set G) := by
    rw [← h_two_elements]
    exact hx
  simp at h_x_in_set
  exact h_x_in_set

/- Let $(G,\cdot)$ be a finite group of order $n$. Show that each element of $G$ is a square if and only if $n$ is odd. -/
theorem number_theory_90289 {G : Type*} [Group G] [Fintype G] :
    (∀ g : G, ∃ x : G, x^2 = g) ↔ Odd (Fintype.card G) := by
  constructor
  · -- Forward direction: Every element is a square implies the group order is odd.
    intro hsquare
    -- Assume the group order is even to derive a contradiction.
    by_contra h_even
    have h_card_even : Even (Fintype.card G) := by exact Nat.not_odd_iff_even.mp h_even
    have h_card_ne_one : Fintype.card G ≠ 1 := by
      intro h_one
      have h_odd : Odd (Fintype.card G) := by rw [h_one]; exact odd_one
      contradiction
    have h_two_dvd : 2 ∣ Fintype.card G := h_card_even.two_dvd
    have h_two_dvd' : 2^1 ∣ Nat.card G := by
      rw [pow_one]
      simp [Nat.card_eq_card_toFinset]
      exact h_card_even.two_dvd
    have h_two_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    -- Use Sylow's theorem to find a subgroup of order $2$.
    have h_subgroup : ∃ H : Subgroup G, Nat.card H = 2 := by
      exact @Sylow.exists_subgroup_card_pow_prime _ _ _ _ 1  h_two_prime h_two_dvd'
    rcases h_subgroup with ⟨H, h_card_H⟩
    -- Prove the subgroup $H$ is a fintype.
    have h_fintype_H : Fintype H := by
      have h_finite_H : Finite H := Nat.finite_of_card_ne_zero (by rw [h_card_H]; exact two_ne_zero)
      exact Fintype.ofFinite H
    have h_card_H' : @Fintype.card H h_fintype_H = 2:= by rwa [Nat.card_eq_fintype_card] at h_card_H
    -- Find a non-identity element a in $H$.
    have h_exists_a : ∃ a : G, a ∈ H ∧ a ≠ 1 := by
      have h_fintype_H : Fintype H := by infer_instance
      have h_card_pos : ↑1 < Fintype.card H := by
        have h_card_eq : Fintype.card H = 2 := by
          have h_nat_card_eq : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
          rw [h_card_H] at h_nat_card_eq
          exact h_nat_card_eq.symm
        rw [h_card_eq]
        exact Nat.one_lt_two
      obtain ⟨a, ha_mem, ha_ne_one⟩ := exists_ne_of_one_lt_card h_card_pos (1 : H)
      have ha_ne_one' : (a : G) ≠ 1 := by
        intro h_eq
        have h_coe_one : ↑(1 : H) = (1 : G) := Subgroup.coe_one H
        rw [← h_coe_one] at h_eq
        apply ha_ne_one
        exact Subtype.coe_injective h_eq
      exact ⟨↑a, a.property, ha_ne_one'⟩
    rcases h_exists_a with ⟨a, ha_in_H, ha_ne_one⟩
    -- Prove that $a^2$ equals the identity.
    have h_a_square_one : a ^ 2 = 1 := by
      have h_a_sq_in_H : a ^ 2 ∈ H := Subgroup.pow_mem H ha_in_H 2
      -- Use lemma to prove H contains only two elements: $1$ and $a$.
      have h_H_elements : ∀ x ∈ H, x = 1 ∨ x = a := by
        apply subgroup_two_elements H h_card_H' a ha_in_H ha_ne_one
      have h_a_sq : a ^ 2 = 1 ∨ a ^ 2 = a := h_H_elements (a ^ 2) h_a_sq_in_H
      -- Analyze the cases for $a^2$, ruling out $a^2 = a$.
      cases h_a_sq with
      | inl h => exact h
      | inr h =>
        have h_a_eq_one : a = 1 := by
          have : a * a = a * 1 := by rw [← pow_two, mul_one]; exact h
          have : a * a * a⁻¹ = a * 1 * a⁻¹ := by rw [this]
          simp [mul_inv_cancel, mul_one] at this
          exact this
        contradiction
    have h_square_one : (1 : G) ^ 2 = 1 := by simp
    have h_not_inj : ¬Function.Injective (fun x : G => x ^ 2) := by
      intro h_inj
      apply ha_ne_one
      apply h_inj
      change a ^ 2 = 1 ^ 2
      rw [h_a_square_one, h_square_one]
    have h_surj_f : Function.Surjective (fun x : G => x ^ 2) := by
      intro g
      obtain ⟨x, hx⟩ := hsquare g
      exact ⟨x, hx⟩
    have h_inj_f : Function.Injective (fun x : G => x ^ 2) := by
      have h_finite : Finite G := by infer_instance
      have h_bijective : Function.Bijective (fun x : G => x ^ 2) :=
        Function.Surjective.bijective_of_finite h_surj_f
      exact h_bijective.1
    contradiction
  · -- Backward direction: Odd group order implies every element is a square.
    intro h_odd
    intro g
    -- Since the group order is odd, the order of element $g$ is also odd.
    have h_order_odd : Odd (orderOf g) := by
      have h_order_dvd : orderOf g ∣ Fintype.card G := orderOf_dvd_card
      exact Odd.of_dvd_nat h_odd h_order_dvd
    -- Construct a square root for $g$.
    let k := (orderOf g + 1) / 2
    have h_k_def : 2 * k = orderOf g + 1 := by
      have h_order_odd' : ∃ m, orderOf g = 2 * m + 1 := by
        rw [Nat.odd_iff] at h_order_odd
        exact ⟨orderOf g / 2, by omega⟩
      obtain ⟨m, h_m⟩ := h_order_odd'
      have h_k_eq : k = m + 1 := by omega
      rw [h_k_eq, h_m]
      ring
    use g ^ k
    -- Verify that $(g^k)^2 = g$.
    have h_square : (g ^ k) ^ 2 = g := by
      rw [← pow_mul, mul_comm, h_k_def]
      have h_order : g ^ orderOf g = 1 := pow_orderOf_eq_one g
      rw [pow_add, h_order, one_mul]
      exact pow_one g
    exact h_square 