import Mathlib

open Finset

/-Find all non-zero natural numbers $a$ and $b$ such that

$$
a^{b}=b^{a^{2}}
$$-/
theorem number_theory_162565 (a b : ℕ) (hne : a ≠ 0 ∧ b ≠ 0) :
    a ^ b = b ^ a ^ 2 ↔ (a, b) = (1, 1) ∨ (a, b) = (2, 16) ∨ (a, b) = (3, 27) := by
  constructor
  -- Assuming the equation, we first show that when $a=1$, $b=1$
  · intro heq; by_cases ha : a = 1
    · simp [ha] at heq
      simp [ha, ← heq]
  -- Now assume $a$ and $b$ are at least $2$, prove they have a same set of prime factors
    replace ha : 2 ≤ a := by omega
    have hb : 2 ≤ b := by
      by_contra!; replace this : b = 1 := by omega
      simp [this] at heq; omega
    have hpf : a.primeFactors = b.primeFactors := by
      apply_fun fun t => t.primeFactors at heq
      repeat rw [Nat.primeFactors_pow] at heq
      exact heq; simp
      all_goals omega
  -- Rewrite $a^2$ and $b$ to multiples of their gcd, prove the multiples and gcd are all positive
    obtain ⟨α, β, copr, hα, hβ⟩ := Nat.exists_coprime (a ^ 2) b
    set d := (a ^ 2).gcd b
    have hpos' : 0 < α ∧ 0 < β ∧ 0 < d := by
      split_ands; all_goals by_contra!; simp at this
      · simp [this] at hα; omega
      · simp [this] at hβ; omega
      simp [this] at hα; omega
  -- Prove that for any prime factors of $a$, there exists some $k$ with $a.factorization p = α * k$ and $b.factorization p = β * k$
    have aux : ∀ p ∈ a.primeFactors, ∃ k, a.factorization p = α * k ∧
    b.factorization p = β * k := by
      intro p hp; apply_fun fun t => t.factorization p at heq
      repeat rw [Nat.factorization_pow] at heq
      simp [hα, hβ] at heq; rw [mul_comm] at heq
      nth_rw 3 [mul_comm] at heq; simp [← mul_assoc] at heq
      rw [← hβ, or_comm] at heq; rcases heq with _|heq
      · omega
      have : α ∣ a.factorization p := by
        rw [← copr.dvd_mul_right, heq]
        simp
      rcases this with ⟨k, hk⟩
      rw [hk, mul_assoc] at heq
      nth_rw 3 [mul_comm] at heq; simp at heq
      rw [mul_comm, or_comm] at heq
      rcases heq with _|heq; omega
      symm at heq; use k
    choose k' hk' using aux
    let k : ℕ → ℕ := fun p => if h : p ∈ a.primeFactors then k' p h else 0
  -- Prove that $a$ and $b$ can be rewritten as $c ^ α$ and $c ^ β$ for some $c$ at least $2$
    let c := ∏ p ∈ a.primeFactors, p ^ k p
    have cpow1 : a = c ^ α := by
      rw [← Nat.factorization_prod_pow_eq_self (show a≠0 by omega)]
      simp [Finsupp.prod]; dsimp [c]
      rw [← prod_pow]; apply prod_congr rfl
      intro p hp; rw [← pow_mul]
      congr 1; dsimp [k]; rw [dite_cond_eq_true]
      rw [(hk' p hp).left, mul_comm]
      exact eq_true hp
    have cpow2 : b = c ^ β := by
      rw [← Nat.factorization_prod_pow_eq_self (show b≠0 by omega)]
      simp [Finsupp.prod]; dsimp [c]
      rw [← prod_pow, ← hpf]; apply prod_congr rfl
      intro p hp; rw [← pow_mul]
      congr 1; dsimp [k]; rw [dite_cond_eq_true]
      rw [(hk' p hp).right, mul_comm]
      exact eq_true hp
    have cge : 2 ≤ c := by
      by_contra!; interval_cases c
      · rw [zero_pow] at cpow1
        all_goals omega
      simp at cpow1; omega
  -- Substitute $a$ and $b$ in `heq`, prove that $β$ is greater then or equal to $2 * α$
    rw [cpow1, cpow2] at heq
    repeat rw [← pow_mul] at heq
    rw [pow_right_inj₀] at heq
    have βge : α * 2 ≤ β := by
      by_contra!; rw [show α * 2 = α * 2 - β + β by omega] at heq
      rw [pow_add] at heq; simp [← mul_assoc] at heq
      rw [or_comm] at heq; rcases heq with _|heq
      · omega
      have βeq : β = 1 := by
        rw [Nat.coprime_comm] at copr
        apply copr.eq_one_of_dvd
        use c ^ (α * 2 - β)
      simp [βeq] at heq cpow2; convert heq
      simp; apply ne_of_lt; calc
        _ < 2 ^ α := Nat.lt_two_pow_self
        _ ≤ 2 ^ (α * 2 - 1) := by
          gcongr; simp; omega
        _ ≤ _ := by gcongr
  -- Simplify `heq` and use `copr` to show $α = 1$
    nth_rw 1 [show β = β - α * 2 + α * 2 by omega] at heq
    rw [pow_add, ← mul_assoc] at heq
    simp at heq; rw [or_comm] at heq
    rcases heq with _|heq; omega
    have αeq : α = 1 := by
      apply copr.eq_one_of_dvd
      rw [← heq]; simp
    simp [αeq] at βge heq cpow1 hα
  -- Prove that $β$ is at most $5$
    have βlt : β ≤ 5 := by
      by_contra!; convert heq
      simp; apply ne_of_gt
      rw [show β - 2 = β - 5 + 3 by omega]
      rw [pow_add]; calc
        _ ≤ (β - 5) * 2 ^ 3 := by omega
        _ < _ := by
          apply Nat.mul_lt_mul_of_lt_of_le
          apply Nat.lt_pow_self; omega
          gcongr; positivity
  -- Discuss all possible values of $β$, then solve for $c$, the goal follows
    interval_cases β; any_goals simp at heq
    · simp [heq] at *
      simp [cpow1, cpow2]
    · rw [show 4 = 2 ^ 2 by rfl] at heq
      rw [pow_left_inj₀] at heq
      simp [heq] at *
      simp [cpow1, cpow2]
      all_goals omega
    · replace heq : 1 ^ 3 < c ^ 3 ∧ c ^ 3 < 2 ^ 3 := by omega
      repeat rw [Nat.pow_lt_pow_iff_left] at heq
      all_goals omega
    all_goals omega
-- Conversely, it is straightforward to check that if $(a, b)$ are of the given values, the equation holds true
  simp; intro h; rcases h with ⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩
  all_goals norm_num [ha, hb]