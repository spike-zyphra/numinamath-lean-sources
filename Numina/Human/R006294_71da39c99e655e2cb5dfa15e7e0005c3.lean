import Mathlib

open Finset

theorem number_theory_635616 (K : ℕ) (hK : K > 0) :
  (∑ i ∈ Finset.range K, 3^(2*i + 1)) % 10 = if Odd K then 3 else 0 := by 
  have h1 (n : ℕ) : 3 ^ (2 * (2 * n) + 1) % 10 = 3 := by 
    induction n with 
    | zero => simp
    | succ m ih =>
      have aux : 2 * (2 * (m + 1)) + 1 = 2 * (2 * m) + 1 + 4 := by omega
      rw [aux, pow_add, Nat.mul_mod, ih]
      omega
  have h2 (n : ℕ) : 3 ^ (2 * (2 * n + 1) + 1) % 10 = 7 := by
    induction n with 
    | zero => simp
    | succ m ih =>
      have aux : 2 * (2 * (m + 1) + 1) + 1 = 2 * (2 * m + 1) + 1 + 4 := by omega
      rw [aux, pow_add, Nat.mul_mod, ih]
      omega
  induction K with 
  | zero => 
    simp
  | succ k ik =>
    by_cases hk0 : k = 0
    -- the case k = 0
    · rw [hk0]
      simp
    -- the case k > 0
    · 
      have kpos : k > 0 := by omega
      obtain ik1 := ik kpos
      have aux : range (k + 1) = insert k (range k) := by
        exact range_add_one
      rw [aux, sum_insert, Nat.add_mod, ik1]
      -- discuss whether k is Odd
      by_cases odd_k : Odd k
      · have nodd : ¬ Odd (k + 1) := by 
          refine Nat.odd_add_one.mp ?_
          ring_nf
          refine Even.add_odd ?_ odd_k
          norm_num
        rw [if_pos odd_k, if_neg nodd]
        obtain ⟨r, hr⟩ := odd_k
        rw [hr, h2]
      · have odd_ksucc : Odd (k + 1) := by 
          exact Nat.odd_add_one.mpr odd_k
        rw [if_neg odd_k, if_pos odd_ksucc]
        simp at odd_k
        obtain ⟨r, hr⟩ := odd_k
        have req : k = 2 * r := by 
          linarith
        rw [req, h1]
      simp