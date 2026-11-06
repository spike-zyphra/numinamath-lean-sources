import Mathlib

open Finset Real

def τ : ℕ → ℕ := fun n => n.divisors.card

theorem number_theory_639489 {n : ℕ} {a : ℕ} (hn : n ≠ 0) :
  (∏ x ∈ (n.divisors), x ^ a) = (√(n ^ (a * (τ n : ℕ)))) := by 
  have h1 : (∏ x ∈ (n.divisors), x ^ a) = (∏ x ∈ (n.divisors), (n / x) ^ a) := by 
    let t : ℕ → ℕ := fun x => n / x
    refine prod_nbij' t t ?_ ?_ ?_ ?_ ?_ 
    · simp
      unfold t
      intro d hd1 hd2
      constructor 
      · obtain ⟨m, hm⟩ := hd1
        use d
        refine Eq.symm (Nat.div_mul_cancel ?_)
        use m 
      exact hd2
    · simp 
      unfold t
      intro d hd1 hd2
      constructor 
      · obtain ⟨m, hm⟩ := hd1
        use d
        refine Eq.symm (Nat.div_mul_cancel ?_)
        use m 
      exact hd2
    · simp 
      intro d hd1 hd2
      unfold t
      exact Nat.div_div_self hd1 hn
    · simp 
      intro d hd1 hd2
      unfold t
      exact Nat.div_div_self hd1 hn
    unfold t
    simp
    intro d hd1 hd2
    rw [Nat.div_div_self hd1 hn]
  have h2 : (∏ x ∈ (n.divisors), x ^ a) * (∏ x ∈ (n.divisors), x ^ a) = 
    (n ^ (a * (τ n : ℕ))) := by 
    nth_rw 2 [h1]
    rw [←prod_mul_distrib]
    calc 
      _ = ∏ x ∈ n.divisors, (x * (n / x)) ^ a := by 
        apply prod_congr rfl
        intro x hx
        simp at hx
        obtain ⟨hx1, hx2⟩ := hx
        rw [mul_pow]
      _ = ∏ x ∈ n.divisors, n ^ a := by
        apply prod_congr rfl
        intro x hx
        simp at hx
        obtain ⟨hx1, hx2⟩ := hx
        have aux : x * (n / x) = n := by 
          obtain ⟨m, hm⟩ := hx1
          rw [hm]
          simp
          left
          rw [mul_comm]
          have neq : x ≠ 0 := by 
            by_contra hc
            simp [hc] at hm
            exact hx2 hm
          exact Eq.symm (Nat.eq_div_of_mul_eq_left neq rfl)
        rw [aux]
      _ = _ := by 
        rw [pow_mul]
        unfold τ 
        exact prod_const (n ^ a)
  have eq1 : (∏ x ∈ n.divisors, x ^ a) ^ 2 = n ^ (a * τ n) := by 
    rw [←h2]
    ring
  have eq2 : ((∏ x ∈ n.divisors, x ^ a : ℝ) : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (a * τ n) := by 
    norm_cast
  have eq3 : (((∏ x ∈ n.divisors, x ^ a : ℝ) : ℝ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = 
    ((n : ℝ) ^ (a * τ n))^ (1 / (2 : ℝ)) := by 
    rw [eq2]
  have aux3 : 0 ≤ ∏ x ∈ n.divisors, (x ^ a : ℝ) := by 
    apply prod_nonneg
    intro i hi
    norm_cast
    omega
  conv at eq3 => 
    lhs
    rw [←rpow_mul aux3]
    simp 
  norm_num
  rw [eq3] 
  exact Eq.symm (sqrt_eq_rpow ((n : ℝ) ^ (a * τ n)))