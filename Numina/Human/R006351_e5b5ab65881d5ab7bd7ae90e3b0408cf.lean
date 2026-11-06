import Mathlib

open Finset Real

/- Let $G$ be a positive integer. Consider the set of all fractions of the form $\frac{1}{pq}$, where $p$ and $q$ are natural numbers such that $p$ and $q$ have greatest common divisor $G$, and $0 < p < q \leq 3G$. Prove that the sum of all such fractions is $\frac{1}{G^2}$. -/
theorem number_theory_636183
  (G : ℕ)
  (hG : 0 < G)
  : let S : Finset (ℕ × ℕ) := { pq ∈ (Icc 1 (3*G)).product (Icc 1 (3*G)) | pq.1≠pq.2 ∧ pq.1.gcd pq.2 = G };
  (∑ pq ∈ S, (1 / (pq.1 * pq.2) : ℚ))/2 = (1 / (G ^ 2) : ℚ) :=
by
  intro S
  -- Get a = p / G and b = q / G
  have genAB : ∀ p > 0, ∀ q > 0, p ≤ 3 * G → q ≤ 3 * G → p ≠ q → Nat.gcd p q = G → ∃ a b, Nat.Coprime a b ∧ p = G * a ∧ q = G * b ∧ a ∈ Icc 1 3 ∧ b ∈ Icc 1 3 ∧ a ≠ b := by
    intro p ppos q qqos pu qu neq H
    use p / G , q / G
    constructor
    . rw [←H]
      apply Nat.coprime_div_gcd_div_gcd
      omega
    constructor
    . rw [←H]
      rw [Nat.mul_div_cancel']
      exact Nat.gcd_dvd_left p q
    constructor
    . rw [←H]
      rw [Nat.mul_div_cancel']
      exact Nat.gcd_dvd_right p q
    constructor
    . simp
      constructor
      . rw [←H]
        refine (Nat.one_le_div_iff ?_).mpr ?_
        . exact Nat.lt_of_lt_of_eq hG (id (Eq.symm H))
        . apply Nat.le_of_dvd
          assumption
          exact Nat.gcd_dvd_left p q
      . have := @Nat.div_le_div_right _ _ G pu
        rw [Nat.mul_div_cancel] at this
        assumption
        assumption
    constructor
    . simp
      constructor
      . rw [←H]
        refine (Nat.one_le_div_iff ?_).mpr ?_
        . exact Nat.lt_of_lt_of_eq hG (id (Eq.symm H))
        . apply Nat.le_of_dvd
          assumption
          exact Nat.gcd_dvd_right p q
      . have := @Nat.div_le_div_right _ _ G qu
        rw [Nat.mul_div_cancel] at this
        assumption
        assumption
    . intro h
      apply_fun (fun x => x * G) at h
      repeat rw [Nat.div_mul_cancel] at h
      tauto
      simp [←H]
      exact Nat.gcd_dvd_right p q
      simp [←H]
      exact Nat.gcd_dvd_left p q
  -- Rewrite S to a listable set S'
  let S' := { ab ∈ (Icc 1 3).product (Icc 1 3) | ab.1 ≠ ab.2 ∧ ab.1.Coprime ab.2}
  let f : ℕ × ℕ ↪ ℕ × ℕ := ⟨ fun (a, b) => (G * a , G * b), ?_⟩
  have : S = S'.map f := by
    simp [S, S']
    ext x
    simp
    constructor
    . rcases x with ⟨p,q⟩
      simp [Finset.product, SProd.sprod]
      intro pb pu qb qu neq H
      have ⟨a, b, h⟩ := genAB p ?_ q ?_ ?_ ?_ ?_ H
      simp at h
      use a, b
      constructor
      constructor
      constructor
      constructor
      all_goals
        try tauto
        try omega
      . simp [f, Function.instFunLikeEmbedding]
        tauto
    . simp [Finset.product, SProd.sprod]
      rintro a b ar ar' br br' neq h hfab 
      rcases x with ⟨p,q⟩
      simp [f, Function.instFunLikeEmbedding] at hfab
      rcases hfab with ⟨hp, hq⟩
      subst hp hq
      repeat constructor
      . simp
        apply Right.one_le_mul hG
        tauto
      . simp
        rw [mul_comm]
        field_simp
        tauto
      constructor
      . simp
        apply Right.one_le_mul hG
        tauto
      . simp
        rw [mul_comm]
        field_simp
        tauto
      constructor
      . simp
        omega
      . simp
        rw [Nat.gcd_mul_left]
        rw [h]
        simp
  rw [this]
  -- compute each elements of S'
  have : S' = {(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)} := by
    decide
  rw [this]
  have : ∀ a b, f (a, b) = (G * a, G * b) := by
    intro a b
    simp [f, Function.instFunLikeEmbedding]
  simp
  simp only [this]
  push_cast
  ring_nf
  simp [Function.Injective]
  intro a b c d h g
  rcases h
  <;> rcases g
  all_goals
    try tauto
    try omega
