import Mathlib

open Nat Finset

theorem my_favorite_theorem (N : ℕ) :
  ((Nat.factorization (Nat.factorial N) 11)) = ∑' k : ℕ, N / 11 ^ (k + 1) := by 
  let b := Nat.log 11 N
  have prime1 : Fact (Nat.Prime 11) := by 
    refine { out := ?_ }
    norm_num
  have ge1 : Nat.log 11 N < b + 1 := by 
    unfold b
    linarith
  -- by the padicValNat_factorial, we get the Legendre formula, padicValNat 11 N ! = ∑ i ∈ Finset.Ico 1 b, N / 11 ^ i
  obtain h1 := padicValNat_factorial ge1
  have h2 : ∑ i ∈ Finset.Ico 1 (b + 1), N / 11 ^ i = ∑ i ∈ Ico 0 b, N / 11 ^ (i + 1) := by 
    let t : ℕ → ℕ := fun n => n - 1
    let s : ℕ → ℕ := fun n => n + 1
    refine sum_nbij' t s ?_ ?_ ?_ ?_ ?_
    · simp
      intro a ha1 ha2 
      unfold t
      omega
    · simp
      intro a ha1
      unfold s
      constructor
      · linarith
      · linarith
    · simp
      intro a ha1 ha2
      unfold s t
      omega
    · simp
      intro a hab
      unfold s t
      simp
    · simp
      intro a ha1 ha2
      unfold t
      have aux : a - 1 + 1 = a := by omega
      rw [aux]
  have h3 : ∑' (k : ℕ), N / 11 ^ (k + 1) =  ∑ i ∈ Ico 0 b, N / 11 ^ (i + 1) := by 
    apply tsum_eq_sum
    intro k hk
    simp at hk
    unfold b at hk
    have aux : 11 ^ (k + 1) > N := by 
      refine lt_pow_of_log_lt ?_ ?_
      norm_num
      omega
    exact div_eq_of_lt aux
  rw [h3, ←h2, ←h1]
  exact rfl