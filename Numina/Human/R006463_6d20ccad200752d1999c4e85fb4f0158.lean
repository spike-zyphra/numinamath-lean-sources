import Mathlib
open Finset Set Nat
noncomputable section

-- Lemma: Apply the Pigeonhole Principle to find two distinct ordered pairs with equal sums modulo N
lemma pigeonhole_pairs (S : Finset ℕ) (N : ℕ)
  (h_card : Finset.card (Finset.range N) < Finset.card (S ×ˢ S)) (hN_pos : N > 0) :
  ∃ p₁ p₂ : ℕ × ℕ, p₁ ∈ S ×ˢ S ∧ p₂ ∈ S ×ˢ S ∧ p₁ ≠ p₂ ∧
    (p₁.1 + p₁.2) % N = (p₂.1 + p₂.2) % N := by
  let f := fun (p : ℕ × ℕ) => (p.1 + p.2) % N
  -- Apply the Pigeonhole Principle using given cardinalities.
  have : ∃ x ∈ S ×ˢ S, ∃ y ∈ S ×ˢ S, x ≠ y ∧ f x = f y := by
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card
    intro ⟨a, b⟩ hab
    simp [f, Finset.mem_product, Finset.mem_range] at hab ⊢
    exact Nat.mod_lt _ hN_pos
  -- Extract the distinct pairs from the Pigeonhole Principle.
  rcases this with ⟨x, hx, y, hy, h_ne, h_eq⟩
  exists x, y

/-Let $m$ be an integer greater than $1$. Let $N = m(m+1)/2$ and $k=m+1$.
Suppose $S$ is a set of $k$ distinct non-negative integers, each of which is strictly less than $N$.
Show that there exist elements $a,b,c,d \in S$ such that the ordered pair $(a,b)$ is not equal to the ordered pair $(c,d)$, and $a+b-c-d$ is divisible by $N$.-/
theorem number_theory_637353 (m : ℕ) (hm : m > 1) (N : ℕ) (hN : N = m * (m + 1) / 2)
  (k : ℕ) (hk : k = m + 1) (S : Finset ℕ) (hS : S.card = k ∧ ∀ x ∈ S, x < N) :
  ∃ a : ℕ, a ∈ S ∧ ∃ b : ℕ, b ∈ S ∧ ∃ c : ℕ, c ∈ S ∧ ∃ d : ℕ, d ∈ S ∧
    (a, b) ≠ (c, d) ∧ N ∣ a + b - c - d := by
  -- Identify the pigeons as the $k^2$ ordered pairs $(a, b)$ in $S × S$.
  have h_pigeons : (S ×ˢ S).card = k ^ 2 := by
    rw [Finset.card_product]
    simp [hS.1]
    rw [pow_two]
  -- Identify the pigeonholes as the $N$ possible values for sums $a + b$ modulo $N$.
  have h_pigeonholes : (Finset.range N).card = N := by
    simp [Finset.card_range]
  -- Verify that the number of pigeons $(k^2)$ is greater than the number of pigeonholes $(N)$.
  have h_more_pigeons : k ^ 2 > N := by
    rw [hk, hN]
    have : m * (m + 1) = 2 * (m * (m + 1) / 2) := by
      have : 2 ∣ m * (m + 1) := by
        have : Even (m * (m + 1)) := Nat.even_mul_succ_self m
        exact Even.two_dvd this
      omega
    rw [this]
    have : (m + 1) ^ 2 > m * (m + 1) := by
      simp
      ring_nf
      linarith
    omega
  -- Apply the Pigeonhole Principle using the external lemma.
  have h_pigeonhole : ∃ (p₁ p₂ : ℕ × ℕ), p₁ ∈ S ×ˢ S ∧ p₂ ∈ S ×ˢ S ∧ p₁ ≠ p₂ ∧
    (p₁.1 + p₁.2) % N = (p₂.1 + p₂.2) % N := by
    have hN_pos : N > 0 := by
      rw [hN]
      have : m * (m + 1) ≥ 4 := by
        have : m ≥ 2 := by linarith
        nlinarith
      omega
    have h_card : Finset.card (Finset.range N) < Finset.card (S ×ˢ S) := by
      rw [h_pigeonholes, h_pigeons]; exact h_more_pigeons
    apply pigeonhole_pairs S N h_card hN_pos
  rcases h_pigeonhole with ⟨⟨a, b⟩, ⟨c, d⟩, hab, hcd, h_ne, h_mod⟩
  -- Prove that $a + b - c - d$ is divisible by $N$ using the modulo equivalence.
  have h_divisible : N ∣ a + b - c - d := by
    simp [Finset.mem_product] at hab hcd
    have h_mod1: (a + b) ≡ (c + d) [MOD N] := by tauto
    have h_mod2: (a + b) - (c + d) ≡ 0 [MOD N] := by
      simp [Nat.ModEq] at h_mod1
      have :  ((a + b) - (c + d)) % N  = 0 := Nat.sub_mod_eq_zero_of_mod_eq h_mod1
      exact this
    have h_eq: (a + b) - (c + d) = a + b - c - d := by omega
    rw [h_eq] at h_mod2
    apply Nat.dvd_of_mod_eq_zero
    exact h_mod2
  simp [Finset.mem_product] at hab hcd
  exists a, hab.1
  exists b, hab.2
  exists c, hcd.1
  exists d, hcd.2
