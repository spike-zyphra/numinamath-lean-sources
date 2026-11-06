import Mathlib

def is_related (a b : ℕ) := ∀ d ∈ Nat.digits 10 (a + b), d = 0 ∨ d = 1

/- We say that two non-negative integers are related if their sum uses only the digits 0 and 1 . For example 22 and 79 are related. Let A and B be two infinite sets of non-negative integers such that: (1) if a $\square \mathrm{A}$ and $\mathrm{b} \square \mathrm{B}$, then a and $\mathrm{b}$ are related, (2) if $\mathrm{c}$ is related to every member of A, then it belongs to $\mathrm{B},(3)$ if $\mathrm{c}$ is related to every member of $\mathrm{B}$, then it belongs to $\mathrm{A}$. Show that in one of the sets $\mathrm{A}, \mathrm{B}$ we can find an infinite number of pairs of consecutive numbers. -/

lemma number_theory_604570_wlog {A B : Set ℕ}
  (hAInf : A.Infinite) (hBInf : B.Infinite)
  (h1 : ∀ a ∈ A, ∀ b ∈ B, is_related a b)
  (h2 : ∀ c, (∀ a ∈ A, is_related c a) → c ∈ B)
  (h4 : ∃ d : ℕ, ∀ a ∈ A, a % 10 = d) :
  {n : ℕ | n ∈ B ∧ n + 1 ∈ B}.Infinite := by

  obtain ⟨d, hd⟩ := h4

  have hB01 : ∀ n ∈ B, (n + d) % 10 = 0 ∨ (n + d) % 10 = 1 := by
    intro n hn
    by_cases hpos : 0 < n + d
    . have : (n + d) % 10 ∈ Nat.digits 10 (n + d) := by
        have := @Nat.digits_of_two_le_of_pos (n + d) 10 (by omega) hpos
        rw [this]
        simp
      have ⟨a, ha, ha_ne_zero⟩ : (A \ {0}).Nonempty := by
        by_contra h
        push_neg at h
        have h2 : A ⊆ {0} := by
          intro a ha
          by_contra h7
          push_neg at h7
          have h8 : a ∈ A \ {0} := by
            simp at *
            all_goals tauto
          rw [h] at h8
          simp at h8
        have h3 : A.Finite := by
          apply Set.Finite.subset (by simp) h2
        contrapose h3
        simpa
      simp at ha_ne_zero
      have h_rel := h1 a ha n hn
      unfold is_related at h_rel
      have : (a + n) % 10 ∈ Nat.digits 10 (a + n) := by
        have := @Nat.digits_of_two_le_of_pos (a + n) 10 (by omega) (by omega)
        rw [this]
        simp
      have := h_rel ((a + n) % 10) this
      rcases this with h | h
      . left
        have := hd a ha
        omega
      . right
        have := hd a ha
        omega

    . simp at hpos
      rw [hpos.1, hpos.2]
      simp

  have h5 : ∀ n ∈ B, (n + d) % 10 = 0 → n + 1 ∈ B := by
    intro n hn hn0
    apply h2
    intro a ha
    have h_rel := h1 a ha n hn
    unfold is_related at h_rel
    unfold is_related

    intro x hx

    by_cases hpos : 0 < a + n
    . have := @Nat.digits_of_two_le_of_pos (n + 1 + a) 10 (by omega) (by omega)
      rw [this] at hx
      simp at hx
      have := hd a ha
      rcases hx with rfl | hx
      . omega
      . rw [show (n + 1 + a) / 10 = (a + n) / 10 by omega] at hx

        have := @Nat.digits_of_two_le_of_pos (a + n) 10 (by omega) hpos
        rw [this] at h_rel
        simp at h_rel
        exact h_rel.2 x hx
    . simp at hpos
      rw [hpos.1, hpos.2] at hx
      simp at hx
      omega

  have h6 : ∀ n ∈ B, (n + d) % 10 = 1 → n - 1 ∈ B := by
    intro n hn hn1
    apply h2
    intro a ha
    have h_rel := h1 a ha n hn
    unfold is_related at h_rel
    unfold is_related

    intro x hx

    by_cases hpos : 0 < n - 1 + a
    . have := @Nat.digits_of_two_le_of_pos (n - 1 + a) 10 (by omega) (by omega)
      rw [this] at hx
      simp at hx
      have := hd a ha
      rcases hx with rfl | hx
      . omega
      . rw [show (n - 1 + a) / 10 = (a + n) / 10 by omega] at hx
        have := @Nat.digits_of_two_le_of_pos (a + n) 10 (by omega) (by omega)
        rw [this] at h_rel
        simp at h_rel
        exact h_rel.2 x hx

    . simp at hpos
      have := hpos.2
      subst a
      have := hpos.1
      interval_cases n
      . simp at hx
      . simp at hx


  rw [Set.infinite_iff_exists_gt]
  intro N
  simp

  rw [Set.infinite_iff_exists_gt] at hBInf
  have ⟨b, hb, hb_gt⟩ := hBInf (N + 1)
  have := hB01 b hb
  rcases this with h | h
  . have := h5 b hb h
    use b
    exact ⟨⟨hb, this⟩, by omega⟩
  . have := h6 b hb h
    use b - 1
    refine ⟨⟨this, ?_⟩, by omega⟩
    rw [show b - 1 + 1 = b by omega]
    exact hb

theorem number_theory_604570
  {A B : Set ℕ}
  (hAInf : A.Infinite) (hBInf : B.Infinite)
  (h1 : ∀ a ∈ A, ∀ b ∈ B, is_related a b)
  (h2 : ∀ c, (∀ a ∈ A, is_related c a) → c ∈ B)
  (h3 : ∀ c, (∀ b ∈ B, is_related c b) → c ∈ A) :
  {n : ℕ | n ∈ A ∧ n + 1 ∈ A}.Infinite
  ∨ {n : ℕ | n ∈ B ∧ n + 1 ∈ B}.Infinite := by

  have ⟨d, hd⟩ : ∃ d : ℕ, (∀ a ∈ A, a % 10 = d) ∨ (∀ b ∈ B, b % 10 = d) := by
    have ⟨a, ha, ha_ne_zero⟩ : (A \ {0}).Nonempty := by
      by_contra h
      push_neg at h
      have h2 : A ⊆ {0} := by
        intro a ha
        by_contra h7
        push_neg at h7
        have h8 : a ∈ A \ {0} := by
          simp at *
          all_goals tauto
        rw [h] at h8
        simp at h8
      have h3 : A.Finite := by
        apply Set.Finite.subset (by simp) h2
      contrapose h3
      simpa
    simp at ha_ne_zero

    let d := a % 10  -- Define the last digit of a

    -- Complement numbers corresponding to d
    let e0 := (10 - d) % 10
    let e1 := (11 - d) % 10

    have hb_digit : ∀ b ∈ B, b % 10 = e0 ∨ b % 10 = e1 := by
      intro b hb

      have hd : (a + b) % 10 ∈ Nat.digits 10 (a + b) := by
        have := @Nat.digits_of_two_le_of_pos (a + b) 10 (by omega) (by omega)
        rw [this]
        simp

      have := h1 a ha b hb
      unfold is_related at this
      have := this ((a + b) % 10) hd
      rcases this with h | h
      . left; omega
      . right; omega

    by_cases h_case1 : (∃ b ∈ B, b % 10 = e0) ∧ (∃ b ∈ B, b % 10 = e1)
    . use d
      left

      intro x hx
      obtain ⟨b0, hb0, hb0_e0⟩ := h_case1.1
      obtain ⟨b1, hb1, hb1_e1⟩ := h_case1.2

      have h_rel0 : (x + b0) % 10 = 0 ∨ (x + b0) % 10 = 1 := by
        by_cases hpos : 0 < x + b0
        . have h_rel0 := h1 x hx b0 hb0
          unfold is_related at h_rel0
          have : (x + b0) % 10 ∈ Nat.digits 10 (x + b0) := by
            have := @Nat.digits_of_two_le_of_pos (x + b0) 10 (by omega) hpos
            rw [this]
            simp
          exact h_rel0 ((x + b0) % 10) this
        . simp at hpos
          rw [hpos.1, hpos.2]
          simp

      have h_rel1 : (x + b1) % 10 = 0 ∨ (x + b1) % 10 = 1 := by
        by_cases hpos : 0 < x + b1
        . have h_rel1 := h1 x hx b1 hb1
          unfold is_related at h_rel1
          have : (x + b1) % 10 ∈ Nat.digits 10 (x + b1) := by
            have := @Nat.digits_of_two_le_of_pos (x + b1) 10 (by omega) hpos
            rw [this]
            simp
          exact h_rel1 ((x + b1) % 10) this
        . simp at hpos
          rw [hpos.1, hpos.2]
          simp

      rcases h_rel0 with h00 | h01
      . rcases h_rel1 with h10 | h11
        . omega
        . omega
      . rcases h_rel1 with h10 | h11
        . omega
        . omega

    . by_cases h_case2 : ∀ b ∈ B, b % 10 = e0
      . use e0
        right
        exact h_case2
      . by_cases h_case3 : ∀ b ∈ B, b % 10 = e1
        . use e1
          right
          exact h_case3
        . simp at h_case1 h_case2 h_case3
          obtain ⟨b1, hb1, hb1_e0⟩ := h_case3
          have := hb_digit b1 hb1
          rcases this with h | h
          . have := h_case1 b1 hb1 h
            use e0
            right
            intro b hb
            have := this b hb
            have := hb_digit b hb
            rcases this with h | h
            . exact h
            . contradiction
          . contradiction

  rcases hd with h | h
  . right
    apply @number_theory_604570_wlog A B
    all_goals try assumption
    use d
  . left
    apply @number_theory_604570_wlog B A
    all_goals try assumption
    . intro a ha b hb
      have := h1 b hb a ha
      unfold is_related at this
      unfold is_related
      intro d hd
      rw [add_comm] at hd
      exact this d hd
    . use d
