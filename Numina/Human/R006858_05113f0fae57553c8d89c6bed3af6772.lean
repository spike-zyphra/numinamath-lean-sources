import Mathlib

open Nat Finset

lemma choose_le_aux (n k: ℕ) (hk : k ≤ n / 2) (hk2 : k ≥ 1) : 
  n.choose k ≥ n.choose 1 := by 
  induction' hk2 with m ih1 ih2
  · simp
  · simp at ih1
    have aux1 : m ≤ n / 2 := by 
      simp at hk
      linarith
    obtain ih3 := ih2 aux1
    have aux2 : m < n / 2 := by 
      simp at hk
      linarith
    obtain h2 := Nat.choose_le_succ_of_lt_half_left aux2
    linarith

theorem number_theory_641820 (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (m : ℕ) 
  (hm : m = p ^ k) :
  ∀ n ≥ m, p ∣ Nat.choose n m - n / m := by 
  intro n hn
  -- first discuss the case for n = k
  by_cases hnm : n = m
  · simp [hnm]
    have aux1 : m / m = 1 := by 
      refine Nat.div_self ?_
      rw [hm]
      refine pos_pow_of_pos k ?_
      exact Prime.pos hp
    rw [aux1]
    simp
  -- the second case that k < n
  -- Choose.choose_modEq_choose_mul_prod_range_choose, use Generalized Lucas's Theorem
  -- For primes p, choose n k is congruent to the product of choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p) over i < a, multiplied by choose (⌊n / p ^ a⌋) (⌊k / p ^ a⌋), modulo p.
  have prime1 : Fact (Nat.Prime p) := by 
    exact { out := hp }
  zify
  rw [Nat.cast_sub]
  obtain h1 := @Choose.choose_modEq_choose_mul_prod_range_choose n m p prime1 k 
  apply Int.ModEq.dvd 
  have eq1 : (∏ i ∈ Finset.range k, (n / p ^ i % p).choose (m / p ^ i % p)) = 1 := by   
    apply prod_eq_one 
    intro x hx
    simp at hx
    have eq_zero : (m / p ^ x % p) = 0 := by 
      rw [hm]
      have aux1 : p ^ k /  p ^ x = p ^ (k - x) := by
        refine Nat.pow_div ?_ ?_
        linarith
        exact pos_of_neZero p
      rw [aux1]
      refine dvd_iff_mod_eq_zero.mp ?_
      refine Dvd.dvd.pow ?_ ?_
      simp
      omega
    rw [eq_zero]
    simp
  simp [eq1] at h1
  have eq2 : (m / p ^ k) = 1 := by 
    rw [hm]
    refine Nat.div_self ?_
    exact pos_of_neZero (p ^ k)
  rw [eq2] at h1
  simp at h1
  
  rw [hm]
  norm_num 
  rw [hm] at h1
  exact id (Int.ModEq.symm h1)
  have kge : m ≥ 1 := by 
    rw [hm]
    exact NeZero.one_le
  have ineq_aux : n.choose m ≥ n := by 
    have ge1 : n.choose m ≥ n.choose 1 := by 
      by_cases hk1 : m ≤ n / 2
      · 
        exact choose_le_aux n m hk1 kge 
      · 
        simp at hk1
        have eq2 : n - m ≤ n / 2 := by 
          omega
        rw [←Nat.choose_symm hn]
        have aux1 : n - m ≥ 1 := by   
          omega
        exact choose_le_aux n (n - m) eq2 aux1
    simp at ge1
    exact ge1
  refine Nat.div_le_of_le_mul ?_
  
  nlinarith