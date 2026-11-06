import Mathlib

theorem number_theory_270407 (n : ℕ) (hn : 2 < n) :
    Even {k | ∃ i, i ∈ Finset.Icc 1 (n - 1) ∧ Nat.Coprime i n ∧ k = i}.ncard := by
  have h1 : {k | ∃ i, i ∈ Finset.Icc 1 (n - 1) ∧ Nat.Coprime i n ∧ k = i} = Finset.filter (fun i => Nat.Coprime i n) (Finset.Icc 1 (n - 1)) := by
    ext k
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  have h3 : Even ((Finset.filter (fun i => Nat.Coprime i n) (Finset.Icc 1 (n - 1))).card) := by
    have h4 : (Finset.filter (fun i => Nat.Coprime i n) (Finset.Icc 1 (n - 1))).card = Nat.totient n := by
      have h5 : (Finset.filter (fun i => Nat.Coprime i n) (Finset.Icc 1 (n - 1))).card = (Finset.filter (fun a => Nat.Coprime n a) (Finset.range n)).card := by 
        have h9 : (Finset.filter (fun i => Nat.Coprime i n) (Finset.Icc 1 (n - 1))) = (Finset.filter (fun a => Nat.Coprime n a) (Finset.range n)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.Coprime]
          constructor
          · -- Show that if $i \in A$, then $i \in B$.
            intro h
            rcases h with ⟨⟨h1, h2⟩, h3⟩
            have h4 : i < n := by
              omega
            have h5 : n.gcd i = 1 := by
              have h6 : i.gcd n = 1 := by
                simpa using h3
              have h7 : n.gcd i = i.gcd n := by 
                rw [show n.gcd i = i.gcd n by simp [Nat.gcd_comm]]
                <;> tauto
              rw [h7, h6]
            exact ⟨h4, h5⟩
          · -- Show that if $i \in B$, then $i \in A$.
            intro h
            rcases h with ⟨h1, h3⟩
            have h4 : 1 ≤ i := by
              by_contra h
              push_neg at h
              have h5 : i = 0 := by
                omega
              rw [h5] at h3
              have h6 : n.gcd 0 = 1 := by
                simpa using h3
              have h7 : n.gcd 0 = n := by
                simp [Nat.gcd_zero_right]
              have h8 : n = 1 := by
                linarith
              omega
            have h4 : 1 ≤ i := by omega
            have h6 : i ≤ n - 1 := by 
              omega
            have h5 : i.gcd n = 1 := by
              have h6 : n.gcd i = 1 := by
                simpa using h3
              have h7 : n.gcd i = i.gcd n := by
                simp [Nat.gcd_comm]
              linarith
            exact ⟨⟨h4, h6⟩, h5⟩
        rw [h9]
        <;> try { simp }
      rw [h5]
      <;> simp [Nat.totient_eq_card_coprime]
      <;> try { omega }
    rw [h4]
    have h7 : n > 2 := by linarith
    have h8 : Even (Nat.totient n) := by
      apply Nat.totient_even
      all_goals
      omega
    exact h8
  exact h3