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

theorem number_theory_638623 (p a : ℕ) (hp : p.Prime) (ha : 0 < a) (k : ℕ) (hk : k = p ^ a) :
  ∀ n ≥ k, p ∣ Nat.choose n k - n / k := by 
  intro n hn
  -- first discuss the case for n = k
  by_cases hnk : n = k
  · simp [hnk]
    have aux1 : k / k = 1 := by 
      refine Nat.div_self ?_
      rw [hk]
      refine pos_pow_of_pos a ?_
      exact Prime.pos hp
    rw [aux1]
    simp
  -- the second case that k < n
  -- Choose.choose_modEq_choose_mul_prod_range_choose, use Generalized Lucas's Theorem
  have prime1 : Fact (Nat.Prime p) := by 
    exact { out := hp }
  zify
  rw [Nat.cast_sub]
  obtain h1 := @Choose.choose_modEq_choose_mul_prod_range_choose n k p prime1 a 
  apply Int.ModEq.dvd 
  have eq1 : (∏ i ∈ Finset.range a, (n / p ^ i % p).choose (k / p ^ i % p)) = 1 := by   
    apply prod_eq_one 
    intro x hx
    simp at hx
    have eq_zero : (k / p ^ x % p) = 0 := by 
      rw [hk]
      have aux1 : p ^ a /  p ^ x = p ^ (a-x) := by
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
  have eq2 : (k / p ^ a) = 1 := by 
    rw [hk]
    refine Nat.div_self ?_
    exact pos_of_neZero (p ^ a)
  rw [eq2] at h1
  simp at h1
  
  rw [hk]
  norm_num 
  rw [hk] at h1
  exact id (Int.ModEq.symm h1)
  have kge : k ≥ 1 := by 
    rw [hk]
    exact NeZero.one_le
  have ineq_aux : n.choose k ≥ n := by 
    have ge1 : n.choose k ≥ n.choose 1 := by 
      by_cases hk1 : k ≤ n / 2
      · 
        exact choose_le_aux n k hk1 kge 
      · 
        simp at hk1
        have eq2 : n - k ≤ n / 2 := by 
          omega
        rw [←Nat.choose_symm hn]
        have aux1 : n - k ≥ 1 := by   
          omega
        exact choose_le_aux n (n-k) eq2 aux1
    simp at ge1
    exact ge1
  refine Nat.div_le_of_le_mul ?_
  
  nlinarith