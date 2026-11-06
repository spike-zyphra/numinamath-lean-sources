import Mathlib

lemma nat_log_eq_log {a b : ℕ} 
  (ha : a ≠ 0)
  (h : Nat.log 2 a = Nat.log 2 b) : b < 2 * a := by
  by_contra hab
  push_neg at hab
  let x := b - 2 * a
  have hx : b = 2 * a + x := by omega
  rw [hx] at h
  have : Nat.log 2 (2 * a) = Nat.log 2 a + 1 := by
    have := @Nat.log_mul_base 2 a (by omega) ha
    rw [mul_comm]
    exact this
  have : Nat.log 2 (2 * a) ≤ Nat.log 2 (2 * a + x) := by
    apply Nat.log_mono_right
    omega
  omega

/- Félix souhaite colorier les entiers de 1 à 2023 tels que si $a, b$ sont deux entiers distincts entre 1 et 2023 and a divise $\mathbf{b}$, alors a et $b$ sont de couleur différentes. Quel est le nombre minimal de couleur dont Félix a besoin? -/
theorem number_theory_607242 :
    IsLeast {n | ∃ f : ℕ → ℕ, (∀ x, f x < n) ∧ (∀ a b, a ∈ Finset.Icc 1 2023 → b ∈ Finset.Icc 1 2023 → a ≠ b → a ∣ b → f a ≠ f b)} 11 := by

  constructor
  . simp
    use fun n => (Nat.log 2 n) % 11
    constructor
    . intro x
      apply Nat.mod_lt
      simp

    . intro a b ha1 ha2 hb1 hb2 hab ⟨k, hk⟩

      by_contra h

      have h1 : Nat.log 2 a = Nat.log 2 b := by
        repeat rw [Nat.mod_eq_of_lt] at h
        . exact h
        . rw [← Nat.lt_pow_iff_log_lt]
          . omega
          . simp
          . omega
        . rw [← Nat.lt_pow_iff_log_lt]
          . omega
          . simp
          . omega

      have := @nat_log_eq_log a b (by omega) h1
      rw [hk] at this
      have : k < 2 := by nlinarith
      interval_cases k
      . simp at hk
        subst b
        simp at hb1
      . rw [hk] at hab
        simp at hab

  . simp [lowerBounds]
    intro n f hf1 hf2
    by_contra hn
    push_neg at hn

    have hn_ne_zero : n ≠ 0 := by
      by_contra h
      subst n
      have := hf1 0
      simp at this


    let powers_of_2 : Finset ℕ := Finset.image (fun i => 2^i) (Finset.range 11)

    have h1 : ∀ x ∈ powers_of_2, 1 ≤ x ∧ x ≤ 2023 := by
      intro x hx
      simp [powers_of_2] at hx
      obtain ⟨a, ha, hx_eq⟩ := hx
      rw [← hx_eq]
      constructor
      . rw [show 1 = 2^0 by omega]
        rw [Nat.pow_le_pow_iff_right]
        . simp
        . simp
      . have : 2^a ≤ 2^10 := by 
          apply Nat.pow_le_pow_right
          . simp
          . omega
        linarith

    have h2 : ∀ x y, x ∈ powers_of_2 → y ∈ powers_of_2 → x < y → x ∣ y := by
      intro x y hx hy hxy
      simp [powers_of_2] at hx hy
      obtain ⟨ax, hax, hx_eq⟩ := hx
      obtain ⟨ay, hay, hy_eq⟩ := hy
      rw [← hx_eq, ← hy_eq]
      apply Nat.pow_dvd_pow
      rw [← hx_eq, ← hy_eq] at hxy
      rw [Nat.pow_lt_pow_iff_right] at hxy
      . omega
      . norm_num

    have h_card : powers_of_2.card = 11 := by
      simp [powers_of_2]
      rw [Finset.card_image_of_injective]
      · simp
      · exact Nat.pow_right_injective (by norm_num : 2 > 1)


    let t := Finset.image f powers_of_2
    have h_card_lt : t.card < powers_of_2.card := by
      rw [h_card]
      suffices t.card ≤ n by omega
      suffices t ⊆ Finset.Icc 0 (n-1) by
        apply Finset.card_mono at this
        simp at this
        rw [show n - 1 + 1 = n by omega] at this
        exact this
      
      intro x hx
      simp [t] at hx
      obtain ⟨a, ha, hx_eq⟩ := hx
      have := hf1 a
      rw [hx_eq] at this
      simp
      omega  


    have h_maps : (∀ a ∈ powers_of_2, f a ∈ t) := by
      intro a ha
      unfold t
      simp
      use a

    have ⟨x, hx_mem, y, hy_mem, hxy_ne, hxy_eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt h_maps
    by_cases h_x_lt_y : x < y
    . have hdvd : x ∣ y := h2 x y hx_mem hy_mem h_x_lt_y
      replace hx_mem := h1 x hx_mem
      replace hy_mem := h1 y hy_mem
      have := hf2 x y hx_mem.1 hx_mem.2 hy_mem.1 hy_mem.2 hxy_ne hdvd
      rw [hxy_eq] at this
      simp at this

    . have h_y_lt_x : y < x := by omega
      have hdvd : y ∣ x := h2 y x hy_mem hx_mem h_y_lt_x
      replace hx_mem := h1 x hx_mem
      replace hy_mem := h1 y hy_mem
      have := hf2 y x hy_mem.1 hy_mem.2 hx_mem.1 hx_mem.2 (Ne.symm hxy_ne) hdvd
      rw [hxy_eq] at this
      simp at this
