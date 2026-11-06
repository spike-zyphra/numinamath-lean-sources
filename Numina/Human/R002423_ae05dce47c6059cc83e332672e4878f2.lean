import Mathlib

/- Let $S$ be the set of all positive integer divisors of $100,000.$ How many numbers are the product of two distinct elements of $S?$
$\textbf{(A) }98\qquad\textbf{(B) }100\qquad\textbf{(C) }117\qquad\textbf{(D) }119\qquad\textbf{(E) }121$ -/
theorem number_theory_93178 (S : Finset ℕ) (hS : S = (Nat.divisors 100000)) :
    {x | ∃ m ∈ S, ∃ n ∈ S, x = m * n ∧ m ≠ n}.ncard = 117 := by

  -- To begin, we notice that 100000 = 2^5 * 5^5, so all divisors have the form 2^x * 5^y
  -- where x, y ≤ 5
  have {a : ℕ} : a ∣ 100000 ↔ ∃ x y : ℕ, a = 2 ^ x * 5 ^ y ∧ x ≤ 5 ∧ y ≤ 5 := by
    rw [show 100000 = 2 ^ 5 * 5 ^ 5 by decide]
    constructor <;> intro h
    · let xx := Nat.gcd a (2 ^ 5)
      let yy := Nat.gcd a (5 ^ 5)
      obtain ⟨x, hx⟩ := (Nat.dvd_prime_pow (by norm_num)).mp <| Nat.gcd_dvd_right a (2 ^ 5)
      obtain ⟨y, hy⟩ := (Nat.dvd_prime_pow (by norm_num)).mp <| Nat.gcd_dvd_right a (5 ^ 5)
      use x, y, ?_, hx.left, hy.left
      rw [← hx.right, ← hy.right, eq_comm]
      apply (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime ?_).mpr h
      norm_num
    · obtain ⟨x, y, rfl, hx, hy⟩ := h
      have : 2 ^ x ∣ 2 ^ 5 := (Nat.pow_dvd_pow_iff_le_right (by decide)).mpr hx
      have : 5 ^ y ∣ 5 ^ 5 := (Nat.pow_dvd_pow_iff_le_right (by decide)).mpr hy
      exact mul_dvd_mul ‹_› ‹_›

  -- This implies that the set {mn | m, n ∈ S, m ≠ n} consists of number of the form
  -- 2^x₁ * 5^y₁ * 2^x₂ * 5^y₂, with x₁, y₁, x₂, y₂ ≤ 5
  have h_rw1 :
      {x | ∃ m ∈ S, ∃ n ∈ S, x = m * n ∧ m ≠ n}
        = (fun ⟨x₁, y₁, x₂, y₂⟩ ↦ 2 ^ x₁ * 5 ^ y₁ * 2 ^ x₂ * 5 ^ y₂) ''
          {(x₁, y₁, x₂, y₂) : ℕ × ℕ × ℕ × ℕ |
            x₁ ≤ 5 ∧ y₁ ≤ 5 ∧ x₂ ≤ 5 ∧ y₂ ≤ 5 ∧ (x₁, y₁) ≠ (x₂, y₂)} := by
    ext x
    simp [hS]
    constructor <;> intro hx
    · obtain ⟨m, hm, n, hn, rfl, hmn⟩ := hx
      obtain ⟨x₁, y₁, h₁⟩ := this.mp hm
      obtain ⟨x₂, y₂, h₂⟩ := this.mp hn
      use x₁, y₁, x₂, y₂
      rw [h₁.left, h₂.left, ← mul_assoc]
      simp [*]
      contrapose! hmn
      rw [hmn.left, hmn.right, ← h₂.left] at h₁
      exact h₁.left
    · obtain ⟨x₁, y₁, x₂, y₂, h⟩ := hx
      simp_rw [this]
      use 2 ^ x₁ * 5 ^ y₁, ?_, 2 ^ x₂ * 5 ^ y₂, ?_
      · simp [← h.right, ← mul_assoc]
        have : x₁ ≠ x₂ ∨ y₁ ≠ y₂ := by tauto
        contrapose! this
        have h₂ := congrArg (fun x ↦ x.factorization 2) this
        have h₅ := congrArg (fun x ↦ x.factorization 5) this
        simp at h₂ h₅
        norm_num at h₂ h₅
        tauto
      · use x₁, y₁, rfl, by tauto, by tauto
      · use x₂, y₂, rfl, by tauto, by tauto

  -- Next, we prove some auxiliary lemmas
  -- Firstly, if n is between 1 and 9, then we can write it as n = a + b, with a and b distinct and
  -- a, b ≤ 5.
  have aux1 (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 9) : ∃ a b : ℕ, a ≤ 5 ∧ b ≤ 5 ∧ a ≠ b ∧ a + b = n := by
    use n - 5, n - (n - 5)
    interval_cases n <;> omega

  -- If n ≤ 10 instead, then we can write it as n = a + b, with a, b ≤ 5.
  have aux2 (n : ℕ) (hn' : n ≤ 10) : ∃ a b : ℕ, a ≤ 5 ∧ b ≤ 5 ∧ a + b = n := by
    use n - 5, n - (n - 5)
    interval_cases n <;> omega

  -- Hence, we can write the pairwise product set as {2^x * 5^y} with x, y ≤ 10 and not both 0 or 10
  have h_rw2 :
      {x | ∃ m ∈ S, ∃ n ∈ S, x = m * n ∧ m ≠ n}
        = (fun ⟨x, y⟩ ↦ 2 ^ x * 5 ^ y) '' {(x, y) : ℕ × ℕ | x ≤ 10 ∧ y ≤ 10 ∧
          ((1 ≤ x ∧ x ≤ 9) ∨ (1 ≤ y ∧ y ≤ 9))} := by
    ext x
    simp [h_rw1]
    constructor <;> intro h
    · obtain ⟨x₁, y₁, x₂, y₂, h, rfl⟩ := h
      use x₁ + x₂, y₁ + y₂, by omega, by ring_nf
    · obtain ⟨x, y, ⟨hx, hy, h⟩, rfl⟩ := h
      cases' h with h h
      · obtain ⟨x₁, x₂, hx₁, hx₂, hx_ne, rfl⟩ := aux1 _ h.left h.right
        obtain ⟨y₁, y₂, hy₁, hy₂, rfl⟩ := aux2 _ hy
        use x₁, y₁, x₂, y₂, by omega, by ring_nf
      · obtain ⟨x₁, x₂, hx₁, hx₂, rfl⟩ := aux2 _ hx
        obtain ⟨y₁, y₂, hy₁, hy₂, hy_ne, rfl⟩ := aux1 _ h.left h.right
        use x₁, y₁, x₂, y₂, by omega, by ring_nf

  -- We also notice that the Set formulation equals the Finset formulation filtering the condition
  have h_card_rw :
      {(x, y) : ℕ × ℕ | x ≤ 10 ∧ y ≤ 10 ∧ (1 ≤ x ∧ x ≤ 9 ∨ 1 ≤ y ∧ y ≤ 9)}
        = (Finset.Icc 0 10 ×ˢ Finset.Icc 0 10).filter
          fun ⟨x, y⟩ ↦ (1 ≤ x ∧ x ≤ 9 ∨ 1 ≤ y ∧ y ≤ 9) := by
    ext ⟨x, y⟩
    simp
    tauto

  -- Hence, we combine all information to compute the size of the pairwise product set of S.
  rw [h_rw2, Set.ncard_image_of_injective, h_card_rw]
  · rw [Set.ncard_coe_Finset]
    decide
  · intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    simp
    intro h
    have h₂ := congrArg (fun x ↦ x.factorization 2) h
    have h₅ := congrArg (fun x ↦ x.factorization 5) h
    simp at h₂ h₅
    norm_num at h₂ h₅
    tauto