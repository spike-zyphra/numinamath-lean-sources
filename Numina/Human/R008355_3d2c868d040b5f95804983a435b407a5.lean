import Mathlib

/- Let $n$ be a positive integer such that $n>2$. Prove that $\varphi(n)$ is even.-/
theorem number_theory_608884 (n : ℕ) (hn : n > 2) : Even (Nat.totient n) := by
  -- Let S, T denotes the numbers coprime to n and less than or equal to n / 2, and the numbers coprime to n and greater than n/2 respectively.
  let S := {x ∈ Finset.range n | Nat.Coprime n x ∧ x ≤ n / 2}
  let T := {x ∈ Finset.range n | Nat.Coprime n x ∧ x > n / 2}
  -- Show that S and T are disjoint.
  have h₀ : Disjoint S T := by
    rw [Finset.disjoint_iff_ne]
    simp [S, T]
    intro i hi j hj
    omega
  -- Show that S and T are equal in size.
  have h₁ : S.card = T.card := by
    refine Finset.card_nbij (fun i => n - i) ?_ ?_ ?_
    . -- Show that the function i => n - i is a function from S to T.
      simp [S, T]
      intro i _ hi' hi''
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      . omega
      . by_contra!
        simp_all
      . rw [Nat.coprime_self_sub_right]
        exact hi'
        omega
      . by_contra!
        -- Assume not, then i ≤ n / 2 and n - i ≤ n / 2 implies that n is even and i = n / 2.
        have h₁ : 2 ∣ n := by
          omega
        obtain ⟨j, h₁⟩ := h₁
        have h₂ : i = j := by
          omega
        rw [show i = n / 2 by omega, Nat.coprime_iff_gcd_eq_one] at hi'
        -- However, n / 2 and n are not coprime, because their gcd is n / 2 > 1.
        have h₃ : Nat.gcd n (n / 2) = n / 2 := by
          rw [<-Nat.gcd_eq_right_iff_dvd]
          nth_rw 2 [show n = n / 2 * 2 by omega]
          apply Nat.dvd_mul_right
        -- This is a contradiction.
        omega
    . -- Show that the function is injective on S.
      intro i hi j hj hij
      simp [S] at hi hj hij
      omega
    . -- Show that the function from S to T is surjective.
      intro j hj
      simp [T] at hj
      use n - j
      simp [S]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      . omega
      . omega
      . -- Show that (n - j) is coprime to n if j is coprime to n.
        rw [Nat.coprime_self_sub_right]
        tauto
        omega
      . -- Show that n - j ≤ n / 2 if n / 2 < j.
        by_contra! hj'
        -- Assume not, derive a contradiction.
        omega
      . omega
  -- Show that S.card + T.card = Nat.totient n.
  have h₂ : Nat.totient n = S.card + T.card := by
    rw [Nat.totient_eq_card_coprime]
    convert Finset.card_union_eq_card_add_card.mpr h₀ using 1
    simp [S, T, Finset.filter_union_right]
    congr
    ext i
    constructor
    . intro hi
      rw [<-and_or_left]
      refine ⟨hi, le_or_lt i (n / 2)⟩
    . rintro (⟨hi, hi'⟩ | ⟨hi, hi'⟩)
      <;> tauto
  rw [even_iff_two_dvd]
  omega