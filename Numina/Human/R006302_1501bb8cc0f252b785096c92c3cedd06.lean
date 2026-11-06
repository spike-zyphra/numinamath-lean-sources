import Mathlib

open Finset

def σ (n : ℕ) := ∑ x ∈ n.divisors, x

/- Key theorem to prove the goal. -/
lemma lemma_1 (m n : ℕ) (hmn : m.Coprime n) :
    σ (m * n) = σ m * σ n :=
by
  simp [σ]
  apply Nat.Coprime.sum_divisors_mul
  assumption

lemma lemma_2 (s : Finset ℕ) (f : ℕ → ℕ) : (s.toList.map f).sum = s.sum f := by
  rw [Finset.sum, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]

lemma lemma_3 : ∀ (s : Finset ℕ), s.toList.sum = ∑ x ∈ s, x := by 
  intro s
  have : ∑ x ∈ s, x = s.sum id := by 
    rfl
  rw [this]
  have : s.toList = s.toList.map id := by 
    exact Eq.symm (List.map_id s.toList)
  rw [this]
  apply lemma_2

/- Let $m$ be a natural number greater than 0 and $p$ be a prime number such that $p$ does not divide $m$. Let $S_m$ denote the sum of the proper divisors of $m$. Determine the sum of the proper divisors of the product $n = m \cdot p$. Show that this sum is $S_m(p+1) + m$. -/
theorem number_theory_635675
  {m p : ℕ}
  (hp : Nat.Prime p)
  (hm : 0 < m)
  (hmp : ¬ p ∣ m)
  (S : ℕ → ℕ)
  (hS : ∀ m, (S m : ℤ) = σ m - m)
  : S (m * p) = S m * (p + 1) + m :=
by
  have : p.Coprime m := by
    apply (Nat.Prime.coprime_iff_not_dvd ?_).mpr
    assumption
    assumption
  have : σ p = 1 + p := by
    simp [σ]
    have : p.divisors = {1,p} := by exact Nat.Prime.divisors hp
    rw [this]
    rw [←lemma_3]
    have : (Finset.toList {1,p}).Perm [1,p] := by
      refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
      . exact nodup_toList {1, p}
      . simp
        intro h
        subst h
        norm_num at hp
      intro a
      constructor
      . simp
      . simp
    rw [List.Perm.sum_eq this]
    simp
  zify
  simp [hS]
  rw [lemma_1, this]
  push_cast
  ring_nf
  simp [Nat.Coprime] at *
  rw [Nat.gcd_comm]
  assumption
